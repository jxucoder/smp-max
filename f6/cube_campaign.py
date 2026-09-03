#!/usr/bin/env python3
"""Production cube-and-conquer campaign for the order-6 refutation.

Refutes "some legal order-6 schedule S has sc(R(S)) >= 49" (the last
unformalized link, REPLAY_DESIGN.md Architecture 3) as a family of
canonical cubes, each with an independently checkable certificate:

    base CNF (sched_sat.build(6, 49)) + unit clauses fixing the first
    steps  --kissat-->  DRAT  --drat-trim-->  LRAT  --cake_lpr-->
    "s VERIFIED UNSAT"

or, with --solver cadical (CaDiCaL's native LRAT output, no drat-trim):

    base + units  --cadical --lrat--> LRAT  --cake_lpr--> "s VERIFIED UNSAT"

cake_lpr's verdict is the certificate either way: it checks the LRAT
against the journaled CNF regardless of which solver produced it.

Cubes
-----
Canonical depth-2 prefixes (S[0] = s1, S[1] = s2) under the first-
appearance rule (a) ONLY: the new men of every step are exactly the next
unused labels as a set.  The backward-commutation rule (b) of
cube_calibrate.py is deliberately NOT applied (it is off the Lean critical
path).  Legality (per-man cap, no-revisit on both sides, move budget) is
the same as cube_calibrate.canonical_depth2.  The "short" cubes
S[0] = stop and S[0] = s1, S[1] = stop (for each canonical s1) complete
the case split.

Coverage claim (precise form).  The root cubes cover every legal schedule
whose first-appearance labeling is the identity: such a schedule is
empty, or of length 1 with a canonical first step, or has a canonical
depth-2 prefix.  An arbitrary legal schedule reduces to one of these via
the schedule-level relabeling lemma (relabel by the first-participation
permutation; legality and the read-off stable count are invariant).
That lemma is formalized so far only at the INSTANCE level (Sym6.lean);
the Lean target theorem is therefore "for every canonical Legal S,
sc(readoffS S) <= 48" plus the relabel reduction.

Adaptive split: a cube that hits the kissat time limit is journaled as
"split" and its canonical depth+1 children (rule (a) extensions plus the
"stop here" child) are enqueued, up to --max-depth.

Journal
-------
Append-only JSONL (--journal), driven by ONE process at a time (see
"Single driver" below).  The first record is a header (status "header")
carrying the base-formula sha256 -- the sha256 of the DIMACS text
`p cnf V C` + clauses exactly as sched_sat.Enc.write and the Lean
exporter print it -- with numVars/numClauses, and the path + sha256 of
sched_sat.py.  Then one record per finished cube, with

    cnf_sha256   sha256 of the CNF file the solver consumed (computed
                 BEFORE the solver runs),
    lrat_sha256  sha256 of the LRAT file cake_lpr verified (verified
                 cubes; also recorded when cake_lpr rejects it),
    solver / solver_version / solver_argv   which solver, its version
                 (+ git commit for cadical) and the exact command line,
    *_rc / *_killed for every subprocess (solver_rc/solver_killed, and
                 kissat_* or cadical_* by name; drattrim_*, cake_*).

Statuses (identical meaning for both solvers; "solver rc" is kissat's or
cadical's exit code: 10 SAT, 20 UNSAT, 0 own time limit).
Terminal (never re-run, except --force with explicit --cubes):
    verified   solver rc 20, [kissat only: drat-trim "s VERIFIED",]
               cake_lpr "s VERIFIED UNSAT";
    SAT        solver rc 10 (see below);
    split      open cube hit the solver time limit; children enqueued.
Non-terminal (recorded, skipped on rerun unless listed in --retry-status,
default "error"):
    timeout_closed  closed cube hit the solver limit (no children; rerun
                    with a larger --time);
    error           solver rc not in {0,10,20} / killed by the wrapper,
                    worker exception, or worker_lost (see below);
    check_timeout   drat-trim or cake_lpr killed by --check-timeout
                    (rerun with a larger --check-timeout);
    drattrim_fail   drat-trim did not print "s VERIFIED" (kissat only);
    cake_fail       cake_lpr did not print "s VERIFIED UNSAT".
A restart skips terminal cubes, re-derives the children of every "split"
record, and re-attempts the --retry-status ones (`--retry-status all`
= every non-terminal status), so the campaign is resumable.

`--audit` checks that the journal covers the whole root cube set (every
root verified, or split with all children recursively covered), that the
header's base sha256 equals the recomputed formula, and that every
"verified" record has solver rc == 20 (kissat_rc or cadical_rc per its
`solver` field), drattrim_verified (kissat records only), cake_verified,
no killed flag, and a cnf_sha256 / lrat_sha256 (defense in depth).  With
--expect-cnf-dir DIR the audit additionally rewrites base + units for
every verified cube into DIR, compares its sha256 with the journaled
cnf_sha256, and, if DIR/c_<tag>.cnf already exists (e.g. printed by the
Lean exporter), compares that file too.  The Lean exporter

    f5/lean/SmpF5/.lake/build/bin/export_sched_cnf OUT --prefix=a,b;c,d

prints DIMACS byte-identical to this driver's CNF for open cubes (same
header, clause order and unit clauses), so a Lean-printed formula can be
cross-checked against the journal cube by cube.  (Closed "stop" cubes add
the unit S[len][0], which `cubeCNFn` does not yet print.)

Any SAT result would be a counterexample to f(6) = 48.  Before anything
is decoded the CNF and the raw model ("v" lines) are copied under
--keep-dir; then the model is decoded (sched_sat.decode) and recounted
independently (read-off ranks + rotation_poset.stable_matchings, cross-
checked with sched_sat.readoff_counts) inside try/except; the record
carries verdict COUNTEREXAMPLE only if exactly K matchings were selected,
each is stable in the recounted read-off and the recount is >= K,
otherwise verdict ENCODING_BUG (reported loudly either way).

Single driver
-------------
One driver per journal: the driver takes an exclusive, non-blocking
flock on <journal>.lock for its lifetime and aborts if another driver
holds it; journal appends are flock-protected and fsync'ed.  A task whose
worker stops reporting for time + 120 + 2*check_timeout + 300 s is
journaled as error/worker_lost and re-enqueued once.

Usage
-----
  python3 cube_campaign.py --count
  python3 cube_campaign.py --dryrun --workers 8 --time 90 --journal dryrun.jsonl
  python3 cube_campaign.py --workers 8 --time 600 --journal campaign.jsonl
  python3 cube_campaign.py --solver cadical --workers 12 --time 600 --journal campaign.jsonl
  python3 cube_campaign.py --retry-status check_timeout,drattrim_fail --check-timeout 14400 ...
  python3 cube_campaign.py --cubes "0,1;2,3" --force --journal campaign.jsonl
  python3 cube_campaign.py --audit [--expect-cnf-dir DIR] --journal campaign.jsonl
  python3 cube_campaign.py --summary --journal campaign.jsonl
"""
import argparse
import tempfile
import signal
import collections
import fcntl
import hashlib
import json
import multiprocessing as mp
import os
import random
import shutil
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from sched_sat import build, cyclic_shapes, decode, readoff_counts  # noqa: E402
from rotation_poset import stable_matchings  # noqa: E402

N = 6
K = 49
BUDGET = N * (N - 1)          # total move budget (30)
PERMAN = N - 1                # per-man cap (5)
DT = os.path.join(HERE, "..", "dt-src", "drat-trim")
CAKE = os.path.join(HERE, "..", "cake_lpr-src", "cake_lpr")
KISSAT = shutil.which("kissat") or "kissat"
CADICAL = os.path.join(HERE, "..", "cadical-src", "build", "cadical")
SOLVERS = ("kissat", "cadical")
SCHED_SAT = os.path.join(HERE, "sched_sat.py")
LEAN_EXPORT = os.path.join(HERE, "..", "f5", "lean", "SmpF5", ".lake", "build", "bin",
                           "export_sched_cnf")

STEPS = cyclic_shapes(N)      # 409 shapes, index j -> S[t][j+1]


# ---------------------------------------------------------------------------
# Cube generation: canonical prefixes under rule (a) only
# ---------------------------------------------------------------------------

def initial_state():
    """(matching, tm, tw, used, moves): identity matching, diagonal visited."""
    return (tuple(range(N)),
            tuple((m,) for m in range(N)),
            tuple((w,) for w in range(N)),
            frozenset(), 0)


def apply_step(state, st):
    """Apply cyclic step `st` (min-first form, m_i takes wife of m_{i+1}).
    Returns the new state or None if illegal / non-canonical.

    Legality: per-man cap, man never revisits a woman, woman never
    revisits a man, total move budget.
    Canonicity (rule (a)): the men appearing for the first time are
    exactly the next unused labels {|used|, ..., |used|+#new-1}.
    """
    matching, tm, tw, used, moves = state
    k = len(st)
    if moves + k > BUDGET:
        return None
    newmen = [m for m in st if m not in used]
    if sorted(newmen) != list(range(len(used), len(used) + len(newmen))):
        return None
    newm = list(matching)
    tm2 = list(tm)
    tw2 = list(tw)
    for i, m in enumerate(st):
        w = matching[st[(i + 1) % k]]
        if len(tm[m]) - 1 >= PERMAN or w in tm[m] or m in tw[w]:
            return None
        newm[m] = w
        tm2[m] = tm[m] + (w,)
        tw2[w] = tw[w] + (m,)
    return (tuple(newm), tuple(tm2), tuple(tw2), used | frozenset(st), moves + k)


def replay(prefix):
    st = initial_state()
    for s in prefix:
        st = apply_step(st, s)
        assert st is not None, f"non-canonical/illegal prefix {prefix}"
    return st


def canonical_children(prefix):
    """All canonical one-step extensions of `prefix` (rule (a) only)."""
    st = replay(prefix)
    return [tuple(prefix) + (s,) for s in STEPS if apply_step(st, s) is not None]


def canonical_prefixes(depth):
    level = [()]
    for _ in range(depth):
        nxt = []
        for p in level:
            nxt.extend(canonical_children(p))
        level = nxt
    return level


def cube_id(prefix, closed):
    parts = [",".join(map(str, s)) for s in prefix]
    if closed:
        parts.append("stop")
    return ";".join(parts) if parts else "stop"


def parse_cube_id(cid):
    parts = cid.split(";")
    closed = parts[-1] == "stop"
    if closed:
        parts = parts[:-1]
    prefix = tuple(tuple(int(x) for x in p.split(",")) for p in parts if p)
    return prefix, closed


def cube_tag(cid):
    """File-name-safe form of a cube id: "0,1;2,3" -> "0-1_2-3"."""
    return cid.replace(";", "_").replace(",", "-")


def cube_units(hooks, prefix, closed):
    """Unit literals fixing S[t] = prefix[t] and, if closed, S[len] = stop."""
    M, V, S, Y, SH, F, P = hooks
    units = []
    for t, s in enumerate(prefix):
        units.append(S[t][SH.index(tuple(s)) + 1])
    if closed:
        units.append(S[len(prefix)][0])
    return units


def root_cubes(depth=2):
    """The complete root case split: open canonical depth-`depth` prefixes
    plus the closed ("stop") cubes at every shorter depth."""
    cubes = []
    level = [()]
    for d in range(depth):
        for p in level:
            cubes.append((p, True))          # stop right after p
        nxt = []
        for p in level:
            nxt.extend(canonical_children(p))
        level = nxt
    for p in level:
        cubes.append((p, False))
    return cubes


def split_children(prefix, closed):
    """Children of a timed-out open cube: stop-here + canonical extensions."""
    assert not closed, "closed cubes have no children"
    return [(tuple(prefix), True)] + [(c, False) for c in canonical_children(prefix)]


# ---------------------------------------------------------------------------
# Hashing / base formula
# ---------------------------------------------------------------------------

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_bytes(*parts):
    h = hashlib.sha256()
    for p in parts:
        h.update(p)
    return h.hexdigest()


def is_sha256(s):
    return isinstance(s, str) and len(s) == 64 and all(c in "0123456789abcdef" for c in s)


_G = {}   # per-process globals: base formula body, hooks, scratch dir, cfg


def _ensure_base():
    if "body" in _G:
        return
    t0 = time.time()
    e, hooks = build(N, K)
    body = "".join(" ".join(map(str, c)) + " 0\n" for c in e.clauses).encode()
    header = f"p cnf {e.n} {len(e.clauses)}\n".encode()
    _G["nvars"] = e.n
    _G["nclauses"] = len(e.clauses)
    _G["body"] = body
    _G["hooks"] = hooks
    # sha256 of the base DIMACS exactly as Enc.write / export_sched_cnf print it
    _G["base_sha256"] = sha256_bytes(header, body)
    _G["sched_sat_sha256"] = sha256_file(SCHED_SAT)
    _G["build_s"] = time.time() - t0


def write_cnf(path, units):
    """base + units as DIMACS (header counts the units)."""
    with open(path, "wb") as f:
        f.write(f"p cnf {_G['nvars']} {_G['nclauses'] + len(units)}\n".encode())
        f.write(_G["body"])
        f.write("".join(f"{u} 0\n" for u in units).encode())


def _tool_version(cmd, flag="--version"):
    try:
        r = subprocess.run([cmd, flag], capture_output=True, text=True, timeout=30)
        return (r.stdout or r.stderr).strip().splitlines()[0][:100]
    except Exception as ex:                  # noqa: BLE001
        return f"unavailable ({ex.__class__.__name__})"


def solver_path(name):
    return KISSAT if name == "kissat" else os.path.abspath(CADICAL)


def solver_version(name):
    """kissat: `kissat --version`; cadical: `cadical --build` first line
    ("Version 3.0.1 <git commit>")."""
    if name == "kissat":
        return _tool_version(KISSAT)
    return _tool_version(solver_path("cadical"), "--build")


def header_record(solver="kissat"):
    _ensure_base()
    return {"status": "header", "ts": time.time(), "n": N, "k": K,
            "num_vars": _G["nvars"], "num_clauses": _G["nclauses"],
            "base_sha256": _G["base_sha256"],
            "sched_sat_path": os.path.abspath(SCHED_SAT),
            "sched_sat_sha256": _G["sched_sat_sha256"],
            "solver": solver, "solver_path": solver_path(solver),
            "solver_version": solver_version(solver),
            "kissat": KISSAT, "kissat_version": _tool_version(KISSAT),
            "cadical": os.path.abspath(CADICAL),
            "cadical_version": solver_version("cadical"),
            "drat_trim": os.path.abspath(DT), "cake_lpr": os.path.abspath(CAKE),
            "lean_exporter": os.path.abspath(LEAN_EXPORT),
            "driver_pid": os.getpid(), "argv": sys.argv[1:]}


# ---------------------------------------------------------------------------
# Worker: one cube end-to-end
# ---------------------------------------------------------------------------

def _worker_init(scratch_root, cfg):
    _ensure_base()
    d = os.path.join(scratch_root, f"w{os.getpid()}")
    os.makedirs(d, exist_ok=True)
    _G["dir"] = d
    _G["cfg"] = cfg


def _run(cmd, timeout):
    """(rc, stdout, stderr, seconds, killed); rc is None iff killed.
    No pipes and no communicate(timeout): stdout/stderr go to temp files,
    the child runs in its own process group, and we poll with a wall-clock
    deadline, SIGKILLing the whole group on expiry (both subprocess.run's
    timeout and communicate(timeout) were observed to leave multi-GB
    cake_lpr checks running for hours on this machine)."""
    t0 = time.time()
    fo = tempfile.TemporaryFile(mode="w+")
    fe = tempfile.TemporaryFile(mode="w+")
    proc = subprocess.Popen(cmd, stdout=fo, stderr=fe, stdin=subprocess.DEVNULL,
                            start_new_session=True)
    killed = False
    deadline = t0 + timeout
    while True:
        rc = proc.poll()
        if rc is not None:
            break
        if time.time() > deadline:
            killed = True
            for sig in (signal.SIGKILL,):
                try:
                    os.killpg(proc.pid, sig)
                except Exception:
                    pass
                try:
                    proc.kill()
                except Exception:
                    pass
            try:
                proc.wait(timeout=60)
            except Exception:
                pass
            rc = None
            break
        time.sleep(0.5)
    def _read(f):
        try:
            f.seek(0)
            return f.read()
        except Exception:
            return ""
        finally:
            try:
                f.close()
            except Exception:
                pass
    out, err = _read(fo), _read(fe)
    return (None if killed else rc), out, err, time.time() - t0, killed


def readoff_ranks(n, sched):
    """Read-off preference ranks of a schedule (mirrors
    sched_sat.readoff_counts, but returns the ranks)."""
    match = list(range(n))
    trajm = [[m] for m in range(n)]
    trajw = [[w] for w in range(n)]
    for sh in sched:
        old = list(match)
        for i, m in enumerate(sh):
            w = old[sh[(i + 1) % len(sh)]]
            match[m] = w
            trajm[m].append(w)
            trajw[w].append(m)
    mrank, wrank = [], []
    for m in range(n):
        order = trajm[m] + [w for w in range(n) if w not in trajm[m]]
        r = [0] * n
        for pos_, w in enumerate(order):
            r[w] = pos_
        mrank.append(r)
    for w in range(n):
        order = list(reversed(trajw[w])) + [m for m in range(n) if m not in trajw[w]]
        r = [0] * n
        for pos_, m in enumerate(order):
            r[m] = pos_
        wrank.append(r)
    return mrank, wrank


def _handle_sat(rec, tag, cnf, out, err, cfg):
    """A SAT cube: keep CNF + raw model first, then decode/recount."""
    keep = os.path.join(cfg["keep_dir"], f"SAT_{tag}")
    os.makedirs(keep, exist_ok=True)
    shutil.copy(cnf, keep)
    vlines = [l for l in out.splitlines() if l.startswith("v ")]
    with open(os.path.join(keep, "model.txt"), "w") as f:
        f.write("\n".join(vlines) + "\n")
    solver = rec.get("solver", "kissat")
    with open(os.path.join(keep, f"{solver}.out"), "w") as f:
        f.write(out)
    with open(os.path.join(keep, f"{solver}.err"), "w") as f:
        f.write(err)
    rec.update({"status": "SAT", "kept": keep, "n_vlines": len(vlines),
                "recount_ok": False, "encoding_bug": True, "verdict": "ENCODING_BUG"})
    try:
        model = [int(x) for l in vlines for x in l[2:].split() if x != "0"]
        sched, sel = decode(model, N, _G["hooks"])
        mrank, wrank = readoff_ranks(N, sched)
        stable = set(tuple(mu) for mu in stable_matchings(mrank, wrank))
        cnt = len(stable)
        cwd = os.getcwd()
        os.chdir(HERE)
        try:
            cnt2 = readoff_counts(N, sched)
        finally:
            os.chdir(cwd)
        unstable = [list(mu) for mu in sel if tuple(mu) not in stable]
        problems = []
        if len(sel) != K:
            problems.append(f"n_selected={len(sel)} != K={K}")
        if len(set(tuple(mu) for mu in sel)) != len(sel):
            problems.append("selected matchings not distinct")
        if unstable:
            problems.append(f"{len(unstable)} selected matchings unstable in recounted read-off")
        if cnt != cnt2:
            problems.append(f"recount mismatch: stable_matchings={cnt} readoff_counts={cnt2}")
        if cnt < K:
            problems.append(f"recount sc={cnt} < K={K}")
        rec.update({"schedule": [list(s) for s in sched], "n_selected": len(sel),
                    "selected": [list(mu) for mu in sel],
                    "selected_unstable": unstable[:10],
                    "recount_sc": cnt, "recount_sc_readoff_counts": cnt2,
                    "problems": problems, "encoding_bug": bool(problems),
                    "recount_ok": not problems,
                    "verdict": "ENCODING_BUG" if problems else "COUNTEREXAMPLE"})
    except Exception as ex:                  # noqa: BLE001
        rec.update({"decode_error": repr(ex), "problems": [f"decode/recount raised {ex!r}"]})
    with open(os.path.join(keep, "record.json"), "w") as f:
        json.dump(rec, f, indent=1)
    return rec



def _split_or_hold(rec, prefix, closed, cfg, reason):
    """A cube whose certificate cannot be checked within budget: split it
    (children have far smaller proofs) unless it is closed or at max depth."""
    rec["reason"] = reason
    if closed:
        rec["status"] = "check_timeout"
        rec["n_children"] = 0
    elif cfg.get("max_depth") is not None and len(prefix) >= cfg["max_depth"]:
        rec["status"] = "timeout_maxdepth"
        rec["n_children"] = 0
    else:
        rec["status"] = "split"
        rec["n_children"] = len(split_children(prefix, closed))
    return rec

def run_cube(task):
    """task = cube_id (str). Returns the journal record (dict)."""
    cid = task
    prefix, closed = parse_cube_id(cid)
    cfg = _G["cfg"]
    d = _G["dir"]
    tag = cube_tag(cid)
    cnf = os.path.join(d, f"c_{tag}.cnf")
    drat = os.path.join(d, f"c_{tag}.drat")
    lrat = os.path.join(d, f"c_{tag}.lrat")
    solver = cfg.get("solver", "kissat")
    rec = {"cube": cid, "prefix": [list(s) for s in prefix], "closed": closed,
           "depth": len(prefix), "worker": os.getpid(), "ts": time.time(),
           "time_limit": cfg["time"], "check_timeout": cfg["check_timeout"],
           "base_sha256": _G["base_sha256"],
           "solver": solver, "solver_path": solver_path(solver),
           "solver_version": cfg.get("solver_version")}
    units = cube_units(_G["hooks"], prefix, closed)
    rec["n_units"] = len(units)
    rec["units"] = units
    write_cnf(cnf, units)
    rec["cnf_bytes"] = os.path.getsize(cnf)
    rec["cnf_sha256"] = sha256_file(cnf)          # provenance: BEFORE solving

    if solver == "kissat":
        # kissat: binary DRAT, converted to LRAT by drat-trim below
        argv = [KISSAT, "-q", f"--time={cfg['time']}", cnf, drat]
    else:
        # cadical: native textual LRAT (the format cake_lpr reads); -t is its
        # own wall-clock limit (rc 0 + "c UNKNOWN", like kissat's --time)
        argv = [solver_path("cadical"), "-q", "-t", str(cfg["time"]),
                "--lrat", "--binary=false", cnf, lrat]
    rec["solver_argv"] = argv
    rc, out, err, dt, killed = _run(argv, timeout=cfg["time"] + 120)
    rec["solve_s"] = round(dt, 2)
    rec["solver_rc"] = rc
    rec["solver_killed"] = killed
    rec[f"{solver}_rc"] = rc
    rec[f"{solver}_killed"] = killed
    rec["drat_bytes"] = os.path.getsize(drat) if os.path.exists(drat) else 0
    if solver == "cadical":
        rec["lrat_bytes"] = os.path.getsize(lrat) if os.path.exists(lrat) else 0

    def cleanup(keep=False):
        if keep:
            return
        for p in (cnf, drat, lrat):
            try:
                os.remove(p)
            except FileNotFoundError:
                pass

    if rc == 10 or "s SATISFIABLE" in out:
        # ---- would be a counterexample to f(6) = 48: keep, then decode/recount
        rec = _handle_sat(rec, tag, cnf, out, err, cfg)
        cleanup(keep=True)
        return rec

    if rc == 0 and not killed:
        # ---- kissat's own --time limit: split (open) / timeout_closed (closed)
        if closed:
            rec["status"] = "timeout_closed"     # no children; needs more time
            rec["n_children"] = 0
        elif cfg.get("max_depth") is not None and len(prefix) >= cfg["max_depth"]:
            # at --max-depth: children would never be enqueued, so keep this
            # NON-terminal; rerun with --retry-status timeout_maxdepth --time T
            rec["status"] = "timeout_maxdepth"
            rec["n_children"] = 0
        else:
            rec["status"] = "split"
            rec["n_children"] = len(split_children(prefix, closed))
        cleanup()
        return rec

    if rc != 20:
        # ---- tool failure (crash, wrapper kill): non-terminal, retried
        rec["status"] = "error"
        rec["reason"] = f"{solver}_killed" if killed else f"{solver}_rc_{rc}"
        rec[f"{solver}_tail"] = out[-1000:] + err[-1000:]
        cleanup(keep=cfg["keep_failures"])
        return rec

    if solver == "kissat":
        # ---- UNSAT: drat-trim -> LRAT, then cake_lpr
        rc2, out2, err2, dt2, killed2 = _run([DT, cnf, drat, "-L", lrat],
                                             timeout=cfg["check_timeout"])
        rec["drattrim_s"] = round(dt2, 2)
        rec["drattrim_rc"] = rc2
        rec["drattrim_killed"] = killed2
        rec["drattrim_verified"] = ("s VERIFIED" in out2) and not killed2
        rec["lrat_bytes"] = os.path.getsize(lrat) if os.path.exists(lrat) else 0
        ratl = [l.strip() for l in out2.splitlines() if "RAT lemmas" in l]
        if ratl:
            rec["drattrim_rat"] = ratl[0]
        if killed2:
            rec["check_stage"] = "drat-trim"
            rec["drattrim_tail"] = out2[-2000:] + err2[-1000:]
            _split_or_hold(rec, prefix, closed, cfg, "check_timeout_drattrim")
            cleanup(keep=cfg["keep_failures"])
            return rec
        if not rec["drattrim_verified"]:
            rec["status"] = "drattrim_fail"
            rec["drattrim_tail"] = out2[-2000:] + err2[-1000:]
            cleanup(keep=cfg["keep_failures"])
            return rec
    # (cadical: the LRAT was written natively by the solver; no drat-trim)
    rec["lrat_bytes"] = os.path.getsize(lrat) if os.path.exists(lrat) else 0
    lim = cfg.get("lrat_split_bytes")
    if lim and rec["lrat_bytes"] > lim and not closed:
        # cake_lpr cost is superlinear in proof size: split instead of checking
        _split_or_hold(rec, prefix, closed, cfg, "lrat_too_large")
        rec["check_stage"] = "cake_lpr(skipped)"
        cleanup()
        return rec
    rec["lrat_sha256"] = sha256_file(lrat)        # the LRAT cake_lpr consumes
    rc3, out3, err3, dt3, killed3 = _run([CAKE, cnf, lrat],
                                         timeout=cfg["check_timeout"])
    rec["cake_s"] = round(dt3, 2)
    rec["cake_rc"] = rc3
    rec["cake_killed"] = killed3
    rec["cake_out"] = out3.strip()[-200:]
    rec["cake_verified"] = ("s VERIFIED UNSAT" in out3) and not killed3
    if killed3:
        rec["check_stage"] = "cake_lpr"
        rec["cake_tail"] = out3[-2000:] + err3[-1000:]
        _split_or_hold(rec, prefix, closed, cfg, "check_timeout_cake")
        cleanup(keep=cfg["keep_failures"])
    elif rec["cake_verified"]:
        rec["status"] = "verified"
        cleanup()
    else:
        rec["status"] = "cake_fail"
        rec["cake_tail"] = out3[-2000:] + err3[-1000:]
        cleanup(keep=cfg["keep_failures"])
    return rec


# ---------------------------------------------------------------------------
# Journal
# ---------------------------------------------------------------------------

TERMINAL = {"verified", "SAT", "split"}
NONTERMINAL = {"timeout_closed", "timeout_maxdepth", "error", "check_timeout", "drattrim_fail", "cake_fail"}


def load_journal(path, with_headers=False):
    """cube id -> last record; with_headers=True also returns the header list."""
    recs, headers = {}, []
    if not os.path.exists(path):
        return (recs, headers) if with_headers else recs
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if r.get("status") == "header":
                headers.append(r)
            elif r.get("cube"):
                recs[r["cube"]] = r       # last record wins
    return (recs, headers) if with_headers else recs


def journal_append(jf, rec):
    """Append one record under an exclusive flock (line-atomic, fsync'ed)."""
    line = json.dumps(rec) + "\n"
    fcntl.flock(jf, fcntl.LOCK_EX)
    try:
        jf.write(line)
        jf.flush()
        os.fsync(jf.fileno())
    finally:
        fcntl.flock(jf, fcntl.LOCK_UN)


def parse_retry(spec):
    if not spec:
        return set()
    names = {s.strip() for s in spec.split(",") if s.strip()}
    if "all" in names:
        return set(NONTERMINAL)
    bad = names - NONTERMINAL
    if bad:
        sys.exit(f"--retry-status: unknown status {sorted(bad)}; "
                 f"choose from {sorted(NONTERMINAL)} or 'all'")
    return names


def summarize(recs, title="summary"):
    by = collections.Counter(r["status"] for r in recs.values())
    ver = [r for r in recs.values() if r["status"] == "verified"]
    solve = sorted(r["solve_s"] for r in recs.values() if "solve_s" in r)
    print(f"== {title}: {len(recs)} cubes  {dict(by)}")
    if solve:
        print(f"   solve_s: median={statistics.median(solve):.1f} "
              f"max={solve[-1]:.1f} mean={statistics.mean(solve):.1f} "
              f"sum={sum(solve):.1f}")
    if ver:
        drat = sorted(r.get("drat_bytes", 0) / 1e6 for r in ver)
        lrat = sorted(r["lrat_bytes"] / 1e6 for r in ver)
        dts = sorted(r["drattrim_s"] for r in ver if "drattrim_s" in r)
        cks = sorted(r["cake_s"] for r in ver)
        bysolver = collections.Counter(r.get("solver", "kissat") for r in ver)
        print(f"   verified {len(ver)} {dict(bysolver)}: "
              f"DRAT median={statistics.median(drat):.1f}MB "
              f"max={drat[-1]:.1f}MB  LRAT median={statistics.median(lrat):.1f}MB "
              f"max={lrat[-1]:.1f}MB  "
              + (f"drat-trim median={statistics.median(dts):.1f}s max={dts[-1]:.1f}s  "
                 if dts else "")
              + f"cake_lpr median={statistics.median(cks):.1f}s max={cks[-1]:.1f}s")
    nonterm = {s: n for s, n in by.items() if s in NONTERMINAL}
    if nonterm:
        print(f"   non-terminal (rerun with --retry-status): {nonterm}")
    for r in recs.values():
        if r["status"] == "SAT":
            print(f"   !!! SAT cube {r['cube']}: verdict={r.get('verdict')} "
                  f"schedule={r.get('schedule')} recount sc={r.get('recount_sc')} "
                  f"problems={r.get('problems')} kept={r.get('kept')}")
    return by


def verify_record(cid, r, base_sha=None):
    """Defense in depth for a 'verified' record: list of problems ([] if ok)."""
    prefix, closed = parse_cube_id(cid)
    p = []
    solver = r.get("solver", "kissat")     # pre-solver-switch records: kissat
    if solver not in SOLVERS:
        p.append(f"unknown solver {solver!r}")
    # UNSAT exit code is 20 for both kissat and cadical (confirmed)
    if r.get(f"{solver}_rc") != 20:
        p.append(f"{solver}_rc={r.get(f'{solver}_rc')}")
    if "solver_rc" in r and r.get("solver_rc") != 20:
        p.append(f"solver_rc={r.get('solver_rc')}")
    if solver == "kissat":
        if r.get("drattrim_verified") is not True:
            p.append("drattrim_verified!=True")
        if r.get("drattrim_rc") != 0:
            p.append(f"drattrim_rc={r.get('drattrim_rc')}")
    if r.get("cake_verified") is not True:
        p.append("cake_verified!=True")
    if r.get("cake_rc") != 0:
        p.append(f"cake_rc={r.get('cake_rc')}")
    for k in (f"{solver}_killed", "solver_killed", "drattrim_killed", "cake_killed"):
        if r.get(k):
            p.append(f"{k}=True")
    if not is_sha256(r.get("cnf_sha256")):
        p.append("missing cnf_sha256")
    if not is_sha256(r.get("lrat_sha256")):
        p.append("missing lrat_sha256")
    if base_sha and r.get("base_sha256") not in (None, base_sha):
        p.append("base_sha256 mismatch")
    if r.get("closed") != closed or r.get("depth") != len(prefix) \
            or r.get("n_units") != len(prefix) + int(closed):
        p.append("prefix/closed/n_units inconsistent with cube id")
    return p


def expected_cnf_sha(cid, expect_dir):
    """Recompute base + units for `cid` as a file under expect_dir and hash it.
    Returns (sha_recomputed, sha_of_preexisting_DIR/c_<tag>.cnf_or_None)."""
    prefix, closed = parse_cube_id(cid)
    units = cube_units(_G["hooks"], prefix, closed)
    tag = cube_tag(cid)
    ext = os.path.join(expect_dir, f"c_{tag}.cnf")
    ext_sha = sha256_file(ext) if os.path.exists(ext) else None
    path = os.path.join(expect_dir, f"expect_c_{tag}.cnf")
    write_cnf(path, units)
    try:
        return sha256_file(path), ext_sha
    finally:
        os.remove(path)


def audit(recs, depth=2, headers=(), expect_dir=None):
    """Coverage check: every root cube must be verified (with a sound
    certificate record), or split with all children (recursively) covered."""
    _ensure_base()
    base_sha = _G["base_sha256"]
    problems = []
    if not headers:
        problems.append("journal has no header record")
    for h in headers:
        if h.get("base_sha256") != base_sha:
            problems.append(f"header base_sha256 {h.get('base_sha256')} != "
                            f"recomputed {base_sha}")
        if (h.get("num_vars"), h.get("num_clauses")) != (_G["nvars"], _G["nclauses"]):
            problems.append("header numVars/numClauses != recomputed")
        if h.get("sched_sat_sha256") != _G["sched_sat_sha256"]:
            problems.append("header sched_sat_sha256 != current sched_sat.py "
                            "(formula sha256 still matches)")
        if "solver" in h:
            print(f"   header: solver={h['solver']} path={h.get('solver_path')} "
                  f"version={h.get('solver_version')!r}")
        else:
            print(f"   header: (pre-solver-switch) kissat={h.get('kissat')} "
                  f"version={h.get('kissat_version')!r}")
    if expect_dir:
        os.makedirs(expect_dir, exist_ok=True)
    roots = root_cubes(depth)
    missing, bad, nver, nexp = [], [], 0, 0
    stack = [cube_id(p, c) for p, c in roots]
    seen = set()
    t0 = time.time()
    while stack:
        cid = stack.pop()
        if cid in seen:
            continue
        seen.add(cid)
        r = recs.get(cid)
        if r is None:
            missing.append(cid)
        elif r["status"] == "verified":
            probs = verify_record(cid, r, base_sha)
            if expect_dir:
                exp, ext = expected_cnf_sha(cid, expect_dir)
                nexp += 1
                if exp != r.get("cnf_sha256"):
                    probs.append(f"recomputed cnf sha256 {exp[:12]} != journaled")
                if ext is not None and ext != r.get("cnf_sha256"):
                    probs.append(f"external c_{cube_tag(cid)}.cnf sha256 {ext[:12]} != journaled")
                if nexp % 500 == 0:
                    print(f"   expect-cnf: {nexp} cubes rehashed, "
                          f"{time.time()-t0:.0f}s", flush=True)
            if probs:
                bad.append((cid, "verified but " + "; ".join(probs)))
            else:
                nver += 1
        elif r["status"] == "split":
            p, c = parse_cube_id(cid)
            stack.extend(cube_id(cp, cc) for cp, cc in split_children(p, c))
        else:
            bad.append((cid, r["status"]))
    print(f"audit: roots={len(roots)} nodes={len(seen)} verified={nver} "
          f"missing={len(missing)} bad={len(bad)} header_problems={len(problems)}"
          + (f" expect-cnf checked={nexp}" if expect_dir else ""))
    for s in problems:
        print(f"   header: {s}")
    for cid, s in bad[:20]:
        print(f"   bad {cid}: {s}")
    for cid in missing[:20]:
        print(f"   missing {cid}")
    hard = [s for s in problems if "sched_sat_sha256" not in s]
    return not missing and not bad and not hard


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--journal", default=os.path.join(HERE, "campaign", "campaign.jsonl"))
    ap.add_argument("--scratch", default=os.path.join(HERE, "campaign", "scratch"))
    ap.add_argument("--keep-dir", default=os.path.join(HERE, "campaign", "keep"))
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--solver", choices=SOLVERS, default="kissat",
                    help="kissat (DRAT -> drat-trim -> LRAT) or cadical (native "
                         "LRAT via --lrat --binary=false, no drat-trim); default kissat")
    ap.add_argument("--time", type=int, default=600,
                    help="solver time limit per cube (s): kissat --time / cadical -t")
    ap.add_argument("--lrat-split-mb", type=int, default=1500,
                    help="open cubes whose LRAT exceeds this size are split instead of checked (0 = off)")
    ap.add_argument("--check-timeout", type=int, default=7200,
                    help="subprocess timeout for drat-trim / cake_lpr (s)")
    ap.add_argument("--depth", type=int, default=2, help="root cube depth")
    ap.add_argument("--max-depth", type=int, default=4,
                    help="deepest cube the adaptive split may create")
    ap.add_argument("--no-split", action="store_true",
                    help="record timeouts as split but do not enqueue children")
    ap.add_argument("--keep-failures", action="store_true",
                    help="keep CNF/DRAT/LRAT of cubes whose certificate failed")
    ap.add_argument("--retry-status", default="error",
                    help="comma-separated non-terminal statuses to re-attempt on a "
                         f"rerun ({','.join(sorted(NONTERMINAL))} or 'all'); default error")
    ap.add_argument("--force", action="store_true",
                    help="with --cubes: re-run the listed cubes even if journaled terminal")
    ap.add_argument("--count", action="store_true", help="print cube counts and exit")
    ap.add_argument("--dryrun", action="store_true",
                    help="24 random depth-2 cubes (seed 0) + the (0,1)+(2,3) cube")
    ap.add_argument("--sample", type=int, default=0,
                    help="run a random sample of this many root cubes")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--cubes", nargs="*", help="explicit cube ids to run")
    ap.add_argument("--audit", action="store_true")
    ap.add_argument("--expect-cnf-dir", default=None,
                    help="with --audit: rewrite base+units per verified cube into DIR and "
                         "compare its sha256 with the journaled cnf_sha256 (also compares "
                         "a pre-existing DIR/c_<tag>.cnf, e.g. printed by export_sched_cnf)")
    ap.add_argument("--summary", action="store_true")
    ap.add_argument("--shuffle", action="store_true",
                    help="randomize the root order (better load balance)")
    args = ap.parse_args()
    if args.force and not args.cubes:
        sys.exit("--force only applies to explicit --cubes")
    retry = parse_retry(args.retry_status)

    roots = root_cubes(args.depth)
    open_roots = [(p, c) for p, c in roots if not c]
    short = [(p, c) for p, c in roots if c]
    print(f"root cubes at depth {args.depth} (rule (a) only): "
          f"open={len(open_roots)} short(stop)={len(short)} total={len(roots)}",
          flush=True)
    if args.count:
        for d in range(1, args.depth + 1):
            print(f"  canonical depth-{d} prefixes: {len(canonical_prefixes(d))}")
        return

    recs, headers = load_journal(args.journal, with_headers=True)
    if args.summary:
        summarize(recs, os.path.basename(args.journal))
        return
    if args.audit:
        ok = audit(recs, args.depth, headers, args.expect_cnf_dir)
        summarize(recs, os.path.basename(args.journal))
        print("audit: " + ("OK" if ok else "FAILED"))
        sys.exit(0 if ok else 1)

    # ---- work list
    forced = set(args.cubes) if args.force else set()

    def should_run(cid):
        r = recs.get(cid)
        if r is None or cid in forced:
            return True
        if r["status"] in TERMINAL:
            return False
        return r["status"] in retry

    if args.cubes:
        todo = list(args.cubes)
    elif args.dryrun:
        rng = random.Random(args.seed)
        sample = rng.sample(open_roots, 24)
        hard = ((0, 1), (2, 3))
        todo = [cube_id(p, c) for p, c in sample] + [cube_id(hard, False)]
    elif args.sample:
        rng = random.Random(args.seed)
        todo = [cube_id(p, c) for p, c in rng.sample(roots, args.sample)]
    else:
        todo = [cube_id(p, c) for p, c in roots]
        if args.shuffle:
            random.Random(args.seed).shuffle(todo)
    # resume: re-derive children of journaled splits, skip finished cubes
    if not args.no_split:
        stack = list(todo)
        seen = set()
        todo = []
        while stack:
            cid = stack.pop(0)
            if cid in seen:
                continue
            seen.add(cid)
            r = recs.get(cid)
            if r is not None and r["status"] == "split" and cid not in forced:
                p, c = parse_cube_id(cid)
                if len(p) < args.max_depth:
                    stack.extend(cube_id(cp, cc) for cp, cc in split_children(p, c))
                continue
            todo.append(cid)
    skipped = collections.Counter(recs[c]["status"] for c in todo
                                  if c in recs and not should_run(c))
    todo = [c for c in todo if should_run(c)]
    print(f"to run: {len(todo)} cubes ({len(recs)} already journaled; "
          f"skipped {dict(skipped)}; retry={sorted(retry)}"
          f"{'; forced ' + str(len(forced)) if forced else ''})", flush=True)
    if not todo:
        summarize(recs, os.path.basename(args.journal))
        return

    os.makedirs(os.path.dirname(os.path.abspath(args.journal)), exist_ok=True)
    args.scratch = os.path.abspath(args.scratch)   # journaled argv is absolute
    os.makedirs(args.scratch, exist_ok=True)
    os.makedirs(args.keep_dir, exist_ok=True)
    if args.solver == "cadical" and not os.access(CADICAL, os.X_OK):
        sys.exit(f"--solver cadical: {os.path.abspath(CADICAL)} not found/executable "
                 "(build cadical-src: ./configure && make)")
    cfg = {"time": args.time, "check_timeout": args.check_timeout,
           "lrat_split_bytes": args.lrat_split_mb * 1000000,
           "keep_dir": args.keep_dir, "keep_failures": args.keep_failures,
           "max_depth": args.max_depth,
           "solver": args.solver, "solver_version": solver_version(args.solver)}
    print(f"solver: {args.solver} {solver_path(args.solver)} "
          f"({cfg['solver_version']})", flush=True)

    # ---- single driver per journal
    lock_path = args.journal + ".lock"
    lockf = open(lock_path, "w")
    try:
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        sys.exit(f"journal {args.journal} is driven by another process "
                 f"(lock {lock_path} held); one driver per journal")
    lockf.write(f"{os.getpid()}\n")
    lockf.flush()

    # Build the base formula ONCE in the parent; with the fork start method
    # the serialized clause body (~46 MB) is inherited copy-on-write by all
    # workers.  (Under spawn the initializer rebuilds it per worker, ~3 s.)
    t0 = time.time()
    _ensure_base()
    print(f"base formula: {_G['nvars']} vars, {_G['nclauses']} clauses, "
          f"{len(_G['body'])/1e6:.1f} MB, sha256 {_G['base_sha256'][:16]}..., "
          f"built in {time.time()-t0:.1f}s", flush=True)

    jf = open(args.journal, "a")
    # ---- header: written once; a journal must never mix base formulas
    for h in headers:
        if h.get("base_sha256") != _G["base_sha256"]:
            sys.exit(f"journal header base_sha256 {h.get('base_sha256')} != "
                     f"current formula {_G['base_sha256']}; refusing to mix formulas")
        if h.get("sched_sat_sha256") != _G["sched_sat_sha256"]:
            print("warning: sched_sat.py changed since the journal header "
                  "(formula sha256 unchanged)", flush=True)
    if not headers:
        hdr = header_record(args.solver)
        journal_append(jf, hdr)
        headers.append(hdr)
        print(f"journal header written: base_sha256={hdr['base_sha256']} "
              f"solver={hdr['solver']} ({hdr['solver_version']})", flush=True)
    elif any(h.get("solver", "kissat") != args.solver for h in headers):
        # allowed (each record names its own solver) but worth a loud note
        print(f"note: journal header solver={headers[0].get('solver', 'kissat')}, "
              f"this run uses --solver {args.solver}; records carry their solver",
              flush=True)

    def stub(cid):
        p, c = parse_cube_id(cid)
        return {"cube": cid, "prefix": [list(s) for s in p], "closed": c,
                "depth": len(p), "ts": time.time(), "time_limit": cfg["time"]}

    ctx = mp.get_context("fork" if "fork" in mp.get_all_start_methods() else "spawn")
    wall = args.time + 120 + 2 * args.check_timeout + 300   # per-task wall bound
    t_start = time.time()
    n_done = 0
    pending, started = {}, {}
    lost = collections.Counter()
    queue = collections.deque(todo)
    with ctx.Pool(args.workers, initializer=_worker_init,
                  initargs=(args.scratch, cfg)) as pool:
        while queue or pending:
            while queue and len(pending) < args.workers:
                cid = queue.popleft()
                pending[cid] = pool.apply_async(run_cube, (cid,))
                started[cid] = time.time()
            now = time.time()
            done = [c for c, a in pending.items() if a.ready() or now - started[c] > wall]
            for cid in done:
                a = pending.pop(cid)
                t_st = started.pop(cid)
                if a.ready():
                    try:
                        rec = a.get()
                    except Exception as ex:         # worker crash: journal + continue
                        rec = stub(cid)
                        rec.update({"status": "error", "reason": "worker_exception",
                                    "error": repr(ex)})
                else:                               # worker stopped reporting
                    rec = stub(cid)
                    rec.update({"status": "error", "reason": "worker_lost",
                                "wall_s": round(now - t_st, 1), "wall_limit": wall})
                    lost[cid] += 1
                    if lost[cid] == 1:
                        queue.append(cid)
                        rec["requeued"] = True
                journal_append(jf, rec)
                recs[cid] = rec
                n_done += 1
                st = rec["status"]
                extra = ""
                if st == "verified":
                    extra = (f"[{rec.get('solver', 'kissat')}] solve={rec['solve_s']}s "
                             + (f"drat={rec['drat_bytes']/1e6:.1f}MB "
                                if rec.get("solver", "kissat") == "kissat" else "")
                             + f"lrat={rec['lrat_bytes']/1e6:.1f}MB "
                             + (f"dt={rec['drattrim_s']}s " if "drattrim_s" in rec else "")
                             + f"cake={rec['cake_s']}s cnf_sha={rec['cnf_sha256'][:12]}")
                elif st == "split":
                    extra = f"{rec.get('reason','timeout')} after {rec.get('solve_s')}s -> {rec['n_children']} children"
                    if not args.no_split and rec["depth"] < args.max_depth:
                        p, c = parse_cube_id(cid)
                        kids = [cube_id(cp, cc) for cp, cc in split_children(p, c)]
                        kids = [k for k in kids if should_run(k)]
                        queue.extend(kids)
                        extra += f" (enqueued {len(kids)})"
                elif st == "SAT":
                    extra = (f"!!!!! SAT: verdict={rec.get('verdict')} "
                             f"schedule={rec.get('schedule')} recount sc={rec.get('recount_sc')} "
                             f"problems={rec.get('problems')} kept={rec.get('kept')}")
                else:
                    extra = json.dumps({k: v for k, v in rec.items()
                                        if k in ("solve_s", "solver", "solver_rc",
                                                 "solver_killed",
                                                 "reason", "error", "check_stage",
                                                 "drattrim_verified", "cake_out",
                                                 "requeued")})
                print(f"[{n_done}/{n_done+len(queue)+len(pending)} "
                      f"{time.time()-t_start:7.1f}s] {cid}: {st} {extra}", flush=True)
            time.sleep(0.2)
    jf.close()
    print(f"done: {n_done} cubes in {time.time()-t_start:.1f}s wall", flush=True)
    by = summarize(recs, os.path.basename(args.journal))
    if by.get("SAT"):
        print("\n" + "!" * 70 + "\n!!! SAT CUBE(S) FOUND -- POSSIBLE COUNTEREXAMPLE TO f(6)=48 "
              "(or ENCODING BUG, see verdict) -- see journal\n" + "!" * 70, flush=True)
    lockf.close()


if __name__ == "__main__":
    main()
