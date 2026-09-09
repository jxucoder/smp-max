#!/usr/bin/env python3
"""Modal driver for the order-6 cube campaign: same worker, same records,
same journal, same audit - only the CPUs are elsewhere.

    modal run tools/campaign/run_modal.py                       # everything left in the journal
    modal run tools/campaign/run_modal.py --sample 50           # 50 random pending cubes (pilot)
    modal run tools/campaign/run_modal.py --cubes "0,1;2,3 stop"
    python3 tools/campaign/run_modal.py --local 3               # 3 cubes in-process, no Modal (toolchain test)

Each remote call runs cube_campaign.run_cube(cid) unchanged inside a
container that has CaDiCaL at the journal header's pinned commit and
cake_lpr built from its hash-checked assembly: write base + units, hash
the CNF before solving, cadical --lrat, hash the LRAT, cake_lpr, delete.
The record (cnf_sha256, lrat_sha256, cadical_rc, cake_verified, ...)
comes back and is appended to the local journal under the same flock the
single-machine driver uses, so `cube_campaign.py --audit` and
merge_journals.py apply verbatim.  Splits are re-enqueued in rounds up to
--max-depth exactly as the local driver does; a SAT record carries the
raw model and the recount verdict back with it.

Money.  Modal bills CPU and memory per second (defaults below are the
public list prices as remembered on 2026-09-05 - override with
--cpu-usd-per-core-hour / --mem-usd-per-gib-hour after checking
modal.com/pricing).  The driver keeps a running estimate from each
record's solve_s + cake_s and stops enqueuing at --budget-usd; set a
spend limit in the Modal dashboard as the hard backstop.
"""

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import argparse
import collections
import fcntl
import json
import os
import random
import statistics
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = str(Path(__file__).resolve().parents[2])
RUNS = os.path.join(ROOT, "runs", "f6")

CADICAL_COMMIT = "c60730422e758ef1cebe7aeddf2dda31c996bf04"
CAKE_S_SHA = "2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a"
CPU_USD_PER_CORE_HOUR = 0.137     # $0.000038 / core / s
MEM_USD_PER_GIB_HOUR = 0.024      # $0.00000667 / GiB / s
MEM_GIB_REQUEST = 4               # request; the limit is higher (cake_lpr peaks ~4 GB RSS)
OVERHEAD_S = 6                    # CNF write + hashing + container amortisation, per cube

RETRY = {"error", "cake_fail", "check_timeout"}
TERMINAL = {"verified", "SAT", "split"}


def worker_cfg(time_limit, check_timeout, lrat_split_mb, max_depth):
    return {"time": time_limit, "check_timeout": check_timeout,
            "lrat_split_bytes": lrat_split_mb * 1000000,
            "keep_dir": "/tmp/keep", "keep_failures": False,
            "max_depth": max_depth, "shard": "modal",
            "solver": "cadical", "solver_version": None}


def run_in_container(cid, cfg, scratch="/tmp/scratch"):
    """The whole per-cube pipeline, in-process.  Used by the Modal method
    and by --local; cube_campaign resolves cadical/cake_lpr relative to its
    own location (../cadical-src, ../cake_lpr-src) on both sides."""
    from tools.campaign import cube_campaign as cc
    if "cfg" not in cc._G or cc._G["cfg"] is not cfg:
        if cfg.get("solver_version") is None:
            cfg["solver_version"] = cc.solver_version("cadical")
        cc._worker_init(scratch, cfg)
    rec = cc.run_cube(cid)
    if rec.get("status") == "SAT" and rec.get("kept"):
        # bring the evidence home: the raw model and the full record
        for name in ("model.txt", "record.json", "cadical.out"):
            p = os.path.join(rec["kept"], name)
            if os.path.exists(p):
                with open(p) as f:
                    rec[f"kept_{name}"] = f.read()[:2_000_000]
    rec["remote_host"] = os.uname().nodename
    return rec


# ---------------------------------------------------------------------------
# Modal side (import guarded so --local works without the package)
# ---------------------------------------------------------------------------
try:
    import modal
except ImportError:                      # --local only
    modal = None

if modal is not None:
    app = modal.App("smp-max-f6-campaign")
    image = (
        modal.Image.debian_slim(python_version="3.11")
        .apt_install("git", "build-essential")
        .run_commands(
            "git clone -q https://github.com/arminbiere/cadical.git /cadical-src",
            f"cd /cadical-src && git checkout -q {CADICAL_COMMIT} && ./configure > /dev/null && make -j > /dev/null",
            f"/cadical-src/build/cadical --build | head -1 | grep -q {CADICAL_COMMIT}",
            "git clone -q https://github.com/tanyongkiam/cake_lpr.git /cake_lpr-src",
            f"cd /cake_lpr-src && echo '{CAKE_S_SHA}  cake_lpr.S' | sha256sum -c - && make cake_lpr > /dev/null 2>&1",
            "/cake_lpr-src/cake_lpr /cake_lpr-src/example.cnf /cake_lpr-src/example.lpr | grep -q 'VERIFIED UNSAT'",
        )
        # Import the checkout package; solver binaries are installed at /.
        .env({"SMP_TOOLCHAIN_ROOT": "/"})
        .add_local_python_source("tools")
    )

    @app.cls(image=image, cpu=1.0, memory=(MEM_GIB_REQUEST * 1024, 8192),
             timeout=4200, max_containers=300, scaledown_window=30, retries=0)
    class Worker:
        @modal.enter()
        def setup(self):
            from tools.campaign import cube_campaign as cc
            self.cc = cc
            cc._ensure_base()

        @modal.method()
        def info(self):
            cc = self.cc
            return {"base_sha256": cc._G["base_sha256"], "num_vars": cc._G["nvars"],
                    "num_clauses": cc._G["nclauses"], "sched_sat_sha256": cc._G["sched_sat_sha256"],
                    "solver_version": cc.solver_version("cadical"),
                    "cadical": cc.solver_path("cadical"), "cake_lpr": os.path.abspath(cc.CAKE)}

        @modal.method()
        def run(self, cid, cfg):
            return run_in_container(cid, cfg)


# ---------------------------------------------------------------------------
# Driver (runs locally; only journal appends touch the disk)
# ---------------------------------------------------------------------------
def build_todo(cc, recs, args, roots):
    if args.cubes:
        todo = args.cubes.split()
    elif args.sample:
        rng = random.Random(args.seed)
        pend = [cube_id for cube_id in (cc.cube_id(p, c) for p, c in roots)]
        todo = pend
    else:
        todo = [cc.cube_id(p, c) for p, c in roots]
    random.Random(args.seed).shuffle(todo)
    # resume: expand journaled splits, skip terminal cubes (as cube_campaign.main)
    stack, seen, out = list(todo), set(), []
    while stack:
        cid = stack.pop(0)
        if cid in seen:
            continue
        seen.add(cid)
        r = recs.get(cid)
        if r is not None and r["status"] == "split":
            p, c = cc.parse_cube_id(cid)
            if len(p) < args.max_depth:
                stack.extend(cc.cube_id(cp, cc2) for cp, cc2 in cc.split_children(p, c))
            continue
        out.append(cid)
    skipped = collections.Counter(recs[c]["status"] for c in out if c in recs
                                  and recs[c]["status"] not in RETRY)
    out = [c for c in out if c not in recs or recs[c]["status"] in RETRY]
    if args.sample:
        out = out[:args.sample]
    return out, skipped


def cost_of(rec, args):
    s = (rec.get("solve_s") or 0) + (rec.get("cake_s") or 0) + OVERHEAD_S
    return s / 3600 * (args.cpu_usd_per_core_hour + MEM_GIB_REQUEST * args.mem_usd_per_gib_hour)


def drive(args, runner, info):
    from tools.campaign import cube_campaign as cc
    recs, headers = cc.load_journal(args.journal, with_headers=True)
    cc._ensure_base()
    if headers and headers[0].get("base_sha256") != cc._G["base_sha256"]:
        sys.exit("journal header base_sha256 != this schedule_encoding.py's formula; refusing")
    if info["base_sha256"] != cc._G["base_sha256"]:
        sys.exit(f"remote base_sha256 {info['base_sha256'][:12]} != local {cc._G['base_sha256'][:12]}")
    roots = cc.root_cubes(2)
    todo, skipped = build_todo(cc, recs, args, roots)
    print(f"roots={len(roots)} journaled={len(recs)} skipped={dict(skipped)} to run={len(todo)}; "
          f"remote solver {info['solver_version']!r}; base sha {info['base_sha256'][:12]} (matches local)",
          flush=True)
    if not todo:
        return
    cfg = worker_cfg(args.time, args.check_timeout, args.lrat_split_mb, args.max_depth)
    cfg["solver_version"] = info["solver_version"]

    os.makedirs(os.path.dirname(os.path.abspath(args.journal)), exist_ok=True)
    lock = open(args.journal + ".lock", "w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        sys.exit(f"{args.journal} is driven by another process (lock held); one driver per journal")
    jf = open(args.journal, "a")
    if not headers:
        hdr = {"status": "header", "ts": time.time(), "n": cc.N, "k": cc.K,
               "num_vars": info["num_vars"], "num_clauses": info["num_clauses"],
               "base_sha256": info["base_sha256"], "sched_sat_path": cc.SCHED_SAT,
               "sched_sat_sha256": info["sched_sat_sha256"], "solver": "cadical",
               "solver_path": info["cadical"], "solver_version": info["solver_version"],
               "cadical": info["cadical"], "cadical_version": info["solver_version"],
               "cake_lpr": info["cake_lpr"], "driver": "modal_campaign.py", "argv": sys.argv[1:]}
        cc.journal_append(jf, hdr)

    spent, n_done, t0 = 0.0, 0, time.time()
    by = collections.Counter()
    queue = list(todo)
    rnd = 0
    while queue:
        rnd += 1
        if args.budget_usd and spent >= args.budget_usd:
            print(f"budget {args.budget_usd} USD reached (est. {spent:.2f}); {len(queue)} cubes left unrun", flush=True)
            break
        batch = queue
        if args.budget_usd and n_done:
            per = spent / n_done
            room = int((args.budget_usd - spent) / per) if per > 0 else len(batch)
            if room < len(batch):
                print(f"budget: this round trimmed from {len(batch)} to {room} cubes", flush=True)
                batch = batch[:room]
        queue = queue[len(batch):]
        print(f"round {rnd}: {len(batch)} cubes", flush=True)
        children = []
        left = len(batch)
        for cid, rec in runner(batch, cfg):
            left -= 1
            if isinstance(rec, BaseException) or rec is None:
                rec = {"cube": cid, "prefix": [list(s) for s in cc.parse_cube_id(cid)[0]],
                       "closed": cc.parse_cube_id(cid)[1], "depth": len(cc.parse_cube_id(cid)[0]),
                       "ts": time.time(), "time_limit": cfg["time"], "status": "error",
                       "reason": "modal_exception", "error": repr(rec)[:2000], "shard": "modal"}
            cc.journal_append(jf, rec)
            recs[rec["cube"]] = rec
            n_done += 1
            spent += cost_of(rec, args)
            st = rec["status"]
            by[st] += 1
            if st == "split" and rec["depth"] < args.max_depth:
                p, c = cc.parse_cube_id(rec["cube"])
                kids = [cc.cube_id(cp, cc2) for cp, cc2 in cc.split_children(p, c)]
                kids = [k for k in kids if k not in recs or recs[k]["status"] in RETRY]
                children.extend(kids)
            extra = ""
            if st == "verified":
                extra = f"solve={rec['solve_s']}s lrat={rec['lrat_bytes']/1e6:.1f}MB cake={rec['cake_s']}s cnf_sha={rec['cnf_sha256'][:12]}"
            elif st == "split":
                extra = f"{rec.get('reason', 'timeout')} -> {rec['n_children']} children"
            elif st == "SAT":
                extra = f"!!!!! SAT verdict={rec.get('verdict')} problems={rec.get('problems')}"
            else:
                extra = json.dumps({k: rec.get(k) for k in ("reason", "error", "check_stage", "cake_out") if rec.get(k)})[:300]
            print(f"[{n_done}/{n_done + left + len(queue) + len(children)} "
                  f"{time.time()-t0:7.1f}s ${spent:7.2f}] {rec['cube']}: {st} {extra}", flush=True)
        queue = children + queue
    jf.close()
    lock.close()
    solve = [r["solve_s"] for r in recs.values() if "solve_s" in r]
    print(f"done: {n_done} cubes in {time.time()-t0:.0f}s, est. cost ${spent:.2f}; {dict(by)}; "
          f"journal now {len(recs)} cubes"
          + (f"; solve median {statistics.median(solve):.1f}s" if solve else ""), flush=True)
    if by.get("SAT"):
        print("!" * 70 + "\n!!! SAT CUBE(S) -- see journal (verdict COUNTEREXAMPLE or ENCODING_BUG)\n" + "!" * 70)


def parse_args(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--journal", default=os.path.join(RUNS, "campaign.jsonl"))
    ap.add_argument("--sample", type=int, default=0, help="run only this many pending cubes (pilot)")
    ap.add_argument("--cubes", default="", help="space-separated explicit cube ids")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--time", type=int, default=300)
    ap.add_argument("--check-timeout", type=int, default=3600)
    ap.add_argument("--lrat-split-mb", type=int, default=1500)
    ap.add_argument("--max-depth", type=int, default=4)
    ap.add_argument("--budget-usd", type=float, default=200.0)
    ap.add_argument("--cpu-usd-per-core-hour", type=float, default=CPU_USD_PER_CORE_HOUR)
    ap.add_argument("--mem-usd-per-gib-hour", type=float, default=MEM_USD_PER_GIB_HOUR)
    ap.add_argument("--local", type=int, default=0,
                    help="run this many pending cubes in-process (no Modal; needs ../cadical-src and ../cake_lpr-src)")
    return ap.parse_args(argv)


def local_runner(batch, cfg):
    for cid in batch:
        try:
            yield cid, run_in_container(cid, cfg, scratch=os.path.join(RUNS, "scratch_modal_local"))
        except Exception as ex:               # noqa: BLE001
            yield cid, ex


def local_info():
    from tools.campaign import cube_campaign as cc
    cc._ensure_base()
    return {"base_sha256": cc._G["base_sha256"], "num_vars": cc._G["nvars"],
            "num_clauses": cc._G["nclauses"], "sched_sat_sha256": cc._G["sched_sat_sha256"],
            "solver_version": cc.solver_version("cadical"), "cadical": cc.solver_path("cadical"),
            "cake_lpr": os.path.abspath(cc.CAKE)}


if modal is not None:
    @app.local_entrypoint()
    def main(journal: str = os.path.join(RUNS, "campaign.jsonl"), sample: int = 0,
             cubes: str = "", seed: int = 0, time_limit: int = 300, check_timeout: int = 3600,
             lrat_split_mb: int = 1500, max_depth: int = 4, budget_usd: float = 200.0,
             cpu_usd_per_core_hour: float = CPU_USD_PER_CORE_HOUR,
             mem_usd_per_gib_hour: float = MEM_USD_PER_GIB_HOUR):
        args = parse_args(["--journal", journal, "--sample", str(sample), "--cubes", cubes,
                           "--seed", str(seed), "--time", str(time_limit),
                           "--check-timeout", str(check_timeout), "--lrat-split-mb", str(lrat_split_mb),
                           "--max-depth", str(max_depth), "--budget-usd", str(budget_usd),
                           "--cpu-usd-per-core-hour", str(cpu_usd_per_core_hour),
                           "--mem-usd-per-gib-hour", str(mem_usd_per_gib_hour)])
        w = Worker()
        info = w.info.remote()

        def runner(batch, cfg):
            # order_outputs=False streams records as containers finish
            for cid, rec in zip(batch, w.run.map(batch, kwargs={"cfg": cfg}, order_outputs=True,
                                                 return_exceptions=True)):
                yield cid, rec
        drive(args, runner, info)


if __name__ == "__main__":
    a = parse_args(sys.argv[1:])
    if not a.local:
        sys.exit("run with `modal run tools/campaign/run_modal.py ...`, or `--local N` for an in-process test")
    a.sample = a.local
    drive(a, local_runner, local_info())
