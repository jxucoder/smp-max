# Order-6 cube campaign (`cube_campaign.py`)

> Historical record from the original repository. Status, paths, and commands below reflect their recorded dates. For current guidance see [results](../results.md), [verification](../verification.md), and the [path migration map](../path-migration.md).

Certified refutation of "some legal order-6 schedule S has sc(R(S)) >= 49"
by cube-and-conquer over canonical schedule prefixes.  Every cube emits
its own certificate chain, checked by cake_lpr, then deleted (f5-style
streaming).  See `REPLAY_DESIGN.md` for the architecture and the pilot.

## Result (2026-09-08): campaign complete, `--audit` OK

Every one of the 25,493 root cubes is certified, directly or through its
adaptive split subtree.  Final journal (`campaign/campaign.jsonl.gz`,
321,701 records; `campaign/audit_final.txt`):

| | |
|---|---|
| distinct cubes | 321,492 (roots 25,493; depth-3 children 197,758; depth-4 children 96,242 + the 139 below) |
| `verified` (cake_lpr `s VERIFIED UNSAT`) | **318,736** |
| `split` | 2,756 (1,804 at depth 2, 952 at depth 3) |
| `SAT` | **0** |
| non-terminal | 0 |
| `--audit` | `roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0`, **exit 0** |

Solver: cadical 3.0.1 `c60730422e758ef1cebe7aeddf2dda31c996bf04` (`--lrat
--binary=false`), checker: cake_lpr (`cake_lpr_arm8.S` sha256
`95b64883…`, the published hash), base formula sha256 `28421fb6…` =
`export_sched_cnf` output; every record carries `cnf_sha256` (hashed
before solving) and `lrat_sha256` (hashed before checking).  Total solver
time 1,076,400 s, median 1.0 s; LRAT median 35 MB, max 9.8 GB (the
certificates were checked and deleted; about 20 TB in total).

Where it ran: container (Linux/x86-64, 4 cores) to 16,694 verified; a
laptop in parallel (3 workers, journal merged on `main`); then this
Mac mini M4 Pro (10 workers, 2026-09-05 20:49 to 2026-09-08 04:10 PDT,
`done: 303935 cubes in 199212.9s`), which alone covers the whole tree.
The 139 depth-4 cubes of the `0,1;2,3` family that hit the 1.5 GB LRAT
cap in the main run (`timeout_maxdepth`) were rerun with

    python3 cube_campaign.py --solver cadical --workers 6 --time 3600 --max-depth 4 \
        --lrat-split-mb 12000 --check-timeout 14400 \
        --retry-status timeout_maxdepth,error,cake_fail,check_timeout \
        --journal campaign/campaign.jsonl --scratch campaign/scratch

and all verified (139/139 in 4,045 s; certificates 1.5 to 9.2 GB, cake_lpr
up to 257 s).  Observed split rates: depth 2, 7.1% (1,804 of 25,339);
depth 3, 0.48% (952 of 197,758); depth 4 never split (cap) - the 0/150
depth-3 probe of 2026-09-05 undercounted because the hard region is
concentrated in a few families (`0,1;2,3` alone: 61 of the first 128
depth-3 splits).

Lean side: `Cubes6.canonicalCubes2` and `extendCanon` print the root set
and every journaled split's children byte-identically
(`export_cubes6`), and `export_sched_cnf [--stop]` reproduces the
journaled `cnf_sha256` of open and closed cubes; the faithfulness proof
that makes the certificates the hypothesis of a Lean theorem is in
progress (`FAITHFULNESS_PLAN.md`, progress log).

## Case split (root cubes)

Canonical prefixes use the first-appearance rule (a) ONLY: the men that
appear for the first time in a step are exactly the next unused labels
(as a set).  Rule (b) (backward commutation) is not applied - it is off
the Lean critical path.  Legality checks (per-man cap 5, no revisit on
either side, 30-move budget) are those of `cube_calibrate.canonical_depth2`.

| set                                   | count  |
|---------------------------------------|--------|
| canonical depth-1 prefixes            | 153    |
| canonical depth-2 prefixes, rule (a)  | 25,339 |
| short cubes: `stop` + `s1;stop`       | 154    |
| **root cubes**                        | 25,493 |

Note on rule (b).  Rule (b) as implemented in `cube_calibrate.py` rejects
a step that is smaller than a man-disjoint predecessor in the
lexicographic *tuple* order.  At depth 2 this is vacuous under rule (a):
if s2 is disjoint from s1 it uses only fresh labels, so min(s2) >
min(s1) = 0 and s2 > s1 as tuples; hence the (a)-only depth-2 set equals
the (a)+(b)-lex set (checked: identical, 25,339).  `gen_enum.c`
implements rule (b) with a different order - the size-first *step-index*
order of its shape table - so its depth-3 count (1,818,512, the number
quoted in `REPLAY_DESIGN.md`) is NOT the (a)+(b)-lex count; the
(a)-only depth-3 count is 1,833,929 (`campaign/depth3_count.log`).  Both
orders give sound prunings (each is a total order on shapes, and the
commutation argument works for any such order), but they select
different canonical representatives, so the counts differ.  The campaign
uses neither: rule (a) alone.

Cube ids: `"0,1;2,3"` = S[0]=(0,1), S[1]=(2,3); `"0,1;stop"` =
S[0]=(0,1), S[1]=stop; `"stop"` = S[0]=stop.  A cube is encoded as the
base CNF plus one unit clause per fixed step (`S[t][SH.index(shape)+1]`,
or `S[t][0]` for stop).  Nothing else is added: symmetry is broken only
through the choice of prefixes.

**Coverage claim, precisely.**  The 25,493 root cubes cover every legal
schedule whose first-appearance labeling is the identity: such a
schedule is empty (`stop`), or has length 1 with a canonical first step
(`s1;stop`), or has a canonical depth-2 prefix.  "Canonical" also means every
step is written in min-first cyclic-shape form (an element of `cyclicShapes`);
Lean's `Legal`/`WFStep` admit any rotation of a step, and rotation-normalising
each step does not change the matching sequence, so this is part of the same
reduction.  Max-depth timeouts are journaled as the non-terminal status
`timeout_maxdepth` and re-attempted with `--retry-status timeout_maxdepth`.
An *arbitrary* legal
schedule reduces to one of these through the schedule-level relabeling
lemma: relabel men by their first-participation order (women
correspondingly); legality is preserved and the read-off stable count
is invariant.  That lemma is formalized so far only at the *instance*
level (`Sym6.lean`: `relabel6` / `mapMu6`, count invariance); the
schedule-level statement is pending.  The Lean target theorem is
therefore

    for every canonical Legal S, sc(readoffS S) <= 48

(discharged by the certificates: the cubes cover exactly the canonical
schedules), plus the relabel reduction from arbitrary to canonical
schedules.  `--audit` checks the journal against the exact root set.

## Per-cube pipeline (worker)

1. write `base + units` as DIMACS (48.7 MB; base clause body is built once
   in the parent and inherited copy-on-write by forked workers) and record
   its sha256 (`cnf_sha256`) **before** solving;
2. `kissat -q --time=T cnf drat` (binary DRAT), or with `--solver cadical`
   `cadical -q -t T --lrat --binary=false cnf lrat` (native text LRAT);
3. rc 20 -> [kissat only: `drat-trim cnf drat -L lrat` (require `s VERIFIED`)]
   -> record `lrat_sha256` -> `cake_lpr cnf lrat` (require `s VERIFIED UNSAT`)
   -> status `verified`, delete cnf/drat/lrat;
4. rc 10 -> status `SAT`: the CNF and the raw model (`v` lines, plus full
   kissat stdout/stderr) are copied under `campaign/keep/SAT_*` *before*
   anything is decoded; then, inside try/except, the model is decoded
   (`sched_sat.decode`) and recounted independently (read-off ranks +
   `rotation_poset.stable_matchings`, cross-checked with
   `sched_sat.readoff_counts`).  Verdict `COUNTEREXAMPLE` only if exactly
   49 matchings were selected, all distinct, each stable in the recounted
   read-off, and the recount is >= 49; any failed check (or a decode
   exception) gives verdict `ENCODING_BUG` with the problems listed.
   Either way it is reported loudly and the record is kept on disk;
5. rc 0 (kissat's own time limit) -> status `split` (open cube) with its
   children = the `stop` child plus all rule-(a) canonical one-step
   extensions; the driver enqueues them (unless `--no-split` or depth ==
   `--max-depth`).  A closed cube that times out is `timeout_closed` (no
   children; rerun with more time);
6. anything else is a tool failure, recorded but NOT terminal:
   `error` (kissat rc not in {0,10,20} or killed by the wrapper),
   `check_timeout` (drat-trim or cake_lpr killed by `--check-timeout`,
   `check_stage` says which), `drattrim_fail`, `cake_fail`.  Every
   subprocess records its rc and a `killed` flag (`kissat_killed`,
   `drattrim_killed`, `cake_killed`).

Terminal statuses are exactly `verified`, `SAT`, `split`.

## Journal, provenance, resume

Append-only JSONL.  The first record is a **header** (`status:
"header"`) with the base-formula sha256 (the DIMACS text `p cnf V C` +
clauses exactly as `sched_sat.Enc.write` prints it), `num_vars` /
`num_clauses`, the path and sha256 of `sched_sat.py`, tool paths and the
kissat version.  A driver refuses to append to a journal whose header
carries a different base sha256.  Then one record per finished cube
(status, times, sizes, checker verdicts, `cnf_sha256`, `lrat_sha256`,
rc/killed flags).

Restarting with the same `--journal` skips every terminal record,
re-derives the children of every `split`, and re-attempts cubes whose
last status is in `--retry-status` (default `error`; e.g.
`--retry-status check_timeout,drattrim_fail --check-timeout 14400`, or
`--retry-status all`).  `--cubes id ... --force` re-runs the listed cubes
even if terminal (last record wins).

`--audit` (exit 0 iff OK) checks: coverage of the exact root set (every
root `verified`, or `split` with all children recursively covered); the
header's base sha256 equals the recomputed formula; and, for every
`verified` record, solver rc == 20 (`kissat_rc` / `cadical_rc` per the
record's `solver`), `drattrim_verified` (kissat records), `cake_rc == 0`
and `cake_verified`, no killed flag, and well-formed `cnf_sha256` /
`lrat_sha256` (defense in depth - the status alone is not trusted).
With `--expect-cnf-dir DIR` the audit also rewrites `base + units` for
every verified cube into DIR, compares its sha256 with the journaled
`cnf_sha256`, and, if `DIR/c_<tag>.cnf` already exists, compares that
file too.  The Lean exporter

    /Users/jiaruixu/work_space/smp-max/f5/lean/SmpF5/.lake/build/bin/export_sched_cnf OUT --prefix=0,1;2,3

prints DIMACS byte-identical to the driver's CNF for open cubes (same
header, clause order, unit clauses), so a Lean-printed formula can be
cross-checked cube by cube against the journaled hashes (closed `stop`
cubes add the unit `S[len][0]`, not yet in `cubeCNFn`).

**Single driver.**  One driver per journal: the driver holds an
exclusive non-blocking `flock` on `<journal>.lock` for its lifetime and
aborts if another driver holds it; each append is flock-protected and
fsync'ed.  A task whose worker stops reporting for
`time + 120 + 2*check_timeout + 300` s is journaled as
`error`/`worker_lost` and re-enqueued once (a pool worker killed by the
OS never completes its `AsyncResult`; this bound covers kissat plus both
checkers at their own limits).

## Dry run (2026-09-02)

24 random canonical depth-2 cubes (seed 0) + the disjoint-transposition
cube `0,1;2,3`, 8 workers, `--time=90`, `--no-split`:

    python3 cube_campaign.py --dryrun --workers 8 --time 90 --no-split \
        --journal campaign/dryrun.jsonl --scratch campaign/scratch_dryrun

Results (`campaign/dryrun.jsonl`, `campaign/dryrun.log`; M4 Max, 16 cores;
pre-provenance driver - these records carry no `cnf_sha256`, so
`--audit` on them fails by design):

| metric                               | value                          |
|--------------------------------------|--------------------------------|
| cubes                                | 25 (24 random + `0,1;2,3`)     |
| verified (cake_lpr `s VERIFIED UNSAT`) | 24 / 24 UNSAT cubes          |
| SAT                                  | 0                              |
| hit the 90 s limit -> `split`        | 1 (`0,1;2,3`, 168 children)    |
| kissat solve (all 25)                | median 3.1 s, mean 9.3 s, max 90 s (limit); max among verified 37.9 s |
| DRAT                                 | median 33 MB, max 250 MB       |
| LRAT                                 | median 174 MB, max 1.10 GB     |
| drat-trim                            | median 112 s, max 350 s        |
| cake_lpr                             | median 5.2 s, max 22.7 s       |
| wall (8 workers)                     | 661 s                          |

All 24 refutations contain RAT lemmas (8k-85k in core), as in the
order-5 pilot; cake_lpr accepts them.

**Finding: drat-trim, not kissat, dominates per-cube cost.**  Backward
checking against the 2.7M-clause base costs 30-100x the solve time
(median 112 s vs 3 s) and is ~85% of per-cube work; cake_lpr is another
~4%.  kissat 4.0.4 has no native LRAT output and no `cadical` binary is
installed, so drat-trim stays in the chain for now.  Budget for the
depth-2 layer at the dry-run mix: 25,339 x ~130 s = ~900 core-hours
(about 3 days on 12 workers, before the hard cubes' split trees, which
add a few hundred core-hours per the calibration in REPLAY_DESIGN.md).
drat-trim and cake_lpr are single-threaded and memory-light, so use
12-14 workers on this machine.  **The CaDiCaL `--lrat` lever**: a
CaDiCaL build with `--lrat` emits LRAT natively (no backward check),
which removes the dominant term and should cut per-cube cost by ~5x;
adding a `--solver` switch to the worker is the cheapest large win if
the budget matters.  (cake_lpr's verdict is unchanged: it checks the
LRAT against the journaled CNF regardless of who produced it.)

## Full campaign (not launched yet)

    cd /Users/jiaruixu/work_space/smp-max/f6
    nohup python3 cube_campaign.py --workers 12 --time 600 --max-depth 4 \
        --shuffle --journal campaign/campaign.jsonl \
        --scratch campaign/scratch > campaign/campaign.log 2>&1 &

    # progress / resume (same command again after any interruption)
    python3 cube_campaign.py --summary --journal campaign/campaign.jsonl
    # re-attempt recorded failures with bigger limits
    python3 cube_campaign.py --retry-status check_timeout,timeout_closed \
        --check-timeout 14400 --time 1800 --journal campaign/campaign.jsonl ...
    # coverage + certificate-record check at the end (exit 0 iff every root
    # cube is certified, directly or through a fully certified split tree)
    python3 cube_campaign.py --audit --journal campaign/campaign.jsonl
    # optional cube-by-cube CNF recomputation (slow: ~0.3 s per cube)
    python3 cube_campaign.py --audit --expect-cnf-dir campaign/expect \
        --journal campaign/campaign.jsonl

Knobs: `--time` (kissat limit per cube), `--max-depth` (deepest adaptive
split, default 4), `--check-timeout` (drat-trim / cake_lpr subprocess
limit, default 7200 s), `--keep-failures` (keep files of cubes whose
certificate did not verify), `--retry-status S[,S]` (non-terminal
statuses to re-attempt, default `error`, or `all`), `--cubes id ...
[--force]` (explicit cubes), `--sample N --seed s` (random subset),
`--expect-cnf-dir DIR` (with `--audit`).

Disk: transient per worker ~50 MB CNF + DRAT + LRAT (LRAT is ~3.5x the
DRAT; the order-5 pilot saw 0.7 GB DRAT / 4.3 GB LRAT for a 4-minute
solve, so budget a few GB per worker for the hardest cubes).

## Provenance check (2026-09-02, `campaign/fixcheck.jsonl`)

Three easy cubes (`stop`, `0,1;stop`, `0,5,4,2,1,3;0,2,5,1,3,4`; 3
workers, `--time 60`) run with the hardened driver, 34 s wall:

- journal = header (base sha256 `28421fb6...`, 84,882 vars / 2,709,212
  clauses, `sched_sat.py` sha256) + three `verified` records, each with
  `kissat_rc 20`, `drattrim_rc 0`, `cake_rc 0`, all killed flags false,
  `cnf_sha256` and `lrat_sha256`;
- rerun of the same command: `to run: 0 cubes (skipped {'verified': 3})`;
- `--cubes <cube> --force --check-timeout 5`: drat-trim killed ->
  `check_timeout` (`check_stage: drat-trim`, `drattrim_killed: true`);
  plain rerun skips it; `--retry-status check_timeout` re-attempts it ->
  `verified` (last record wins);
- a second driver on the same journal aborts on the `.lock`;
- `export_sched_cnf ... --prefix=0,5,4,2,1,3;0,2,5,1,3,4` (37 s) printed
  a file with sha256 `f2ea077c...` = the journaled `cnf_sha256`, and
  `--audit --expect-cnf-dir` reported `bad=0` for all three (the audit
  as a whole fails only on the 25,490 roots not yet run).

Not an easy cube: `0,1;0,2` hits a 60 s limit and splits into 140
children (the `(0,1)` family again, cf. the calibration).

## Solver choice (2026-09-02): `--solver cadical` (native LRAT)

`cube_campaign.py --solver {kissat,cadical}` (default kissat, path
unchanged).  The cadical path runs

    cadical-src/build/cadical -q -t T --lrat --binary=false cnf lrat

(CaDiCaL rel-3.0.1, commit c60730422e758ef1cebe7aeddf2dda31c996bf04,
built from `cadical-src/` with `./configure && make`; `cadical-src/` must
be gitignored like `dt-src/` and `cake_lpr-src/`), then `cake_lpr cnf lrat`
directly on the solver's textual LRAT: no drat-trim.  Exit codes are the
same as kissat's (10 SAT, 20 UNSAT, 0 = its own `-t` limit, printing
`c UNKNOWN`), so the status mapping is identical (`verified`, `SAT`,
`split` / `timeout_closed` / `timeout_maxdepth`, `error`).  Every record
carries `solver`, `solver_version` (`cadical --build` line: version +
git commit), the exact `solver_argv`, `solver_rc`/`solver_killed` plus
`cadical_rc`/`cadical_killed` (or `kissat_*`), `cnf_sha256` (before
solving) and `lrat_sha256` (hashed before cake_lpr).  `--audit` accepts
a `verified` record iff its solver's rc is 20, `cake_rc == 0` with
`cake_verified`, no killed flag, and both hashes are present; kissat
records additionally need `drattrim_rc == 0` + `drattrim_verified`.
The header records `solver`, `solver_path`, `solver_version` (and both
solvers' versions).  cake_lpr's verdict is the certificate either way.

Measured (M4 Max, single core per cube; cake_lpr = `cake_lpr-src/cake_lpr`):

| instance                        | chain            | solve   | LRAT     | drat-trim | cake_lpr | verdict          |
|---------------------------------|------------------|---------|----------|-----------|----------|------------------|
| order-5 pilot (n=5,k=17)        | kissat+drat-trim | 156-236 s | 4.3 GB | 267 s     | 83 s     | s VERIFIED UNSAT |
| order-5 pilot (n=5,k=17)        | cadical --lrat   | 150 s   | 4.35 GB  | -         | 93 s     | s VERIFIED UNSAT |
| order-6 `stop`                  | cadical --lrat   | 0.4 s   | 14.7 MB  | -         | 2.1 s    | s VERIFIED UNSAT |
| order-6 `0,5,4,2,1,3;0,2,5,1,3,4` (Lean-exported CNF, sha `f2ea077c...`) | cadical --lrat | 0.6 s | 39.4 MB | - | 2.4 s | s VERIFIED UNSAT |
| order-6 `0,1;2,3` (hard)        | cadical --lrat, `--time 300` | 300 s (limit) | 13.2 GB (transient, deleted) | - | - | `split` -> 168 children (not closed; kissat did not close it in 560 s either) |

Per-cube cost at order 5 drops from ~500-590 s to ~245 s (the drat-trim
term is gone; cake_lpr is unchanged since the LRAT is the same size).
At order 6 the dry run's drat-trim median of 112 s per cube (~85% of
per-cube work) disappears, so the depth-2 layer budget falls from
~900 core-hours to roughly the solve + cake_lpr time (~10-20 s median
per cube, i.e. of the order of 100 core-hours at the dry-run mix).

Caveats.  (1) CaDiCaL's LRAT is written eagerly during search, at
~40 MB/s on the hard cube: a cube that runs to a 600 s limit leaves a
~25 GB transient LRAT per worker (deleted on timeout), so budget disk for
`--workers x 25 GB` on hard layers, or lower `--time` there.  (2) The
text LRAT is ~3.5x kissat's DRAT, but no larger than drat-trim's LRAT
was.  (3) cadical does not print a `v` model line with `-n`; the driver
does not pass `-n`, so a SAT cube still records its model.

Driver check (`campaign/cadical_check.jsonl`, `campaign/cadical_check.log`;
3 workers, `--time 120`): `stop`, `0,1;stop`, `0,5,4,2,1,3;0,2,5,1,3,4`
all `verified` in 5.9 s wall (solve 0.4-0.7 s, LRAT 14.7-39.4 MB,
cake_lpr 4.8 s each; the third cube's `cnf_sha256` equals the Lean
exporter's `f2ea077c...`); `--audit` reports `bad=0 header_problems=0`
(fails only on the 25,490 roots not run).  The kissat path and the audit
of pre-switch journals (`campaign/fixcheck.jsonl`) are unchanged
(re-run: 2 cubes verified, `bad=0`).  The hard-cube run is journaled in
`campaign/cadical_hard.jsonl`.

Full campaign with cadical:

    nohup python3 cube_campaign.py --solver cadical --workers 12 --time 600 \
        --max-depth 4 --shuffle --journal campaign/campaign.jsonl \
        --scratch campaign/scratch > campaign/campaign.log 2>&1 &

## Toolchain reproduction on Linux/x86-64 (2026-09-05)

The campaign was built and driven on an Apple M4 Max.  Rebuilt from
source in a clean Linux/x86-64 container (Ubuntu 24.04, gcc 13.3, 4
cores) to check that nothing in the chain is machine-specific:

- `cadical-src` at the pinned commit `c60730422e758ef1cebe7aeddf2dda31c996bf04`
  (`./configure && make`) reports `Version 3.0.1 c6073042…`, i.e. the exact
  `solver_version` string in the journal header;
- `cake_lpr-src` built with the repo's default x64 target
  (`gcc -O2 basis_ffi.c cake_lpr.S`); `cake_lpr example.cnf example.lpr`
  gives `s VERIFIED UNSAT`.  Note that upstream's own `cake_lpr.sha256` is
  stale for `basis_ffi.c` (commit `a36874a`, 2026-07-22, replaced the
  heap/stack environment variables with `--CML_HEAP_SIZE=` /
  `--CML_STACK_SIZE=` flags without refreshing the checksum file); the
  CakeML-generated `cake_lpr.S` still matches its published hash
  `2f3af32d…`, and the FFI shim is outside the trust base in any case;
- the base formula rebuilds to sha256 `28421fb6…` (84,882 vars /
  2,709,212 clauses), matching the journal header, so `--audit` passes its
  header checks off the original machine;
- two cubes already `verified` on the M4 Max, re-run here with `--force`
  into a throwaway journal, reproduced their journaled `cnf_sha256`
  byte for byte (`0,5,4,3,2,1;0,3,5,1,4,2` -> `e1efd2e120f6`,
  `0,2,5,1,3,4;0,1,2,4,5` -> `cc0edf551f57`), with identical LRAT sizes
  (39.1 MB / 55.8 MB) and `s VERIFIED UNSAT` both times.

Relative speed on this container: solve ~1.6x slower than the M4 Max,
cake_lpr ~2.2x slower (22.5 s vs 10.3 s on the same cube).

**Journal forking.**  A resume in a second location starts from the same
committed snapshot, so the two journals are additive, not conflicting:
merging is a concatenation (the loader keeps the last record per cube,
and every record here is terminal and independently checkable).  Parallel
drivers will re-derive the same split children and may duplicate some
work; nothing is invalidated.  The `flock` guard is per-filesystem, so it
does not prevent this - only one driver per journal *file*.

## Depth-3 pricing probe (2026-09-05, `campaign/depth3_probe.jsonl`)

The depth-2 layer splits at 4.7%, and each split replaces one cube with
~110 children, so the campaign's total size is set by the split rate one
level down - which had never been measured: at the depth-2 rate the tree
grows to ~460k nodes with a depth-4 layer `--max-depth` forbids from
splitting; if depth-3 cubes simply close, it is ~145k.

150 cubes drawn uniformly (seed 20260905) from the 70,282 children of the
631 journaled split parents, campaign knobs (`--time 300`, 1.5 GB LRAT
watchdog), `--max-depth 3` so a cube that would split is journaled
`timeout_maxdepth` instead of enqueuing children.  Linux/x86-64
container, 3 workers, 633 s wall:

| metric | depth-3 probe | depth-2 layer (for comparison) |
|---|---|---|
| verified | **150 / 150** | 12,727 |
| **split** | **0** (95% CI upper bound 2.0%, rule of three) | 4.7% |
| solve | median 1.5 s, mean 2.7 s, max 18.5 s | median 2.7 s, mean 14.8 s |
| cake_lpr | median 8.5 s, mean 9.4 s, max 20.5 s | median 4.9 s, mean 20.5 s |
| solve+cake | median 10.0 s, **mean 12.2 s** | mean 35.3 s |
| LRAT | median 36.6 MB, max 338 MB | median 107 MB, max 9.8 GB |

Every record carries `cadical_rc 20`, `cake_verified`, `cnf_sha256` and
`lrat_sha256`; no killed flags.  (Two of the 150 are the depth-2 `stop`
children of split parents, which is what a uniform draw over the child
population gives.)

**Fixing one step more makes a cube roughly three times cheaper and, on
this evidence, closes it.**  Restricting the schedule prefix cuts the
proof rather than merely displacing it: LRAT drops 3x and cake_lpr - not
the solver - becomes the dominant term (77% of per-cube cost at depth 3).

Projection with these numbers: 12,107 roots left, plus ~133,600 depth-3
cubes (the 70,282 children already enqueued, plus ~571 further splits
among the remaining roots at the observed 4.7%), so **~146k cubes and
~584 core-hours** on this container's cores - 8 days at 3 workers, about
a day across eight such containers, and a depth-4 layer that on present
evidence may not exist at all.  The earlier ~460k-node worry is
unsupported: it assumed the depth-2 split rate recurred at depth 3, and
0/150 rules that rate out at better than 95% confidence.

## Sharding across containers (2026-09-05)

The laptop is out; the campaign runs in ephemeral Linux containers (4
cores, ~190-300 nodes/h each at 3 workers).  `cube_campaign.py --shard
I/N` restricts a driver to the roots with sha256(id) mod N == I.  The
partition is by **root**: a root's whole adaptive split subtree is run by
the shard that owns the root (children are enqueued in-process by the
driver that journals the split and, on resume, re-derived only from that
journal's own split records), so N drivers on N journals seeded from the
same snapshot never run the same root, and the union of their journals is
a complete campaign journal.  Every record carries its `shard`.

`merge_journals.py -o merged.jsonl campaign.jsonl shards/*.jsonl.gz`
merges any number of journals, **in any order**: one header (mixed
`base_sha256` refused); per cube exactly one record, the best by
SAT > verified > split > non-terminal and then latest `ts`.  Order
independence matters: a root this container split by a wall-clock
timeout (40 of the first 665 splits are `-t 300` timeouts) can be
verified outright by a faster shard, and a `split` must never shadow a
certificate - the audit would demand children nobody ran.  Torn trailing
lines (a checkpoint taken mid-append) are skipped and counted.  The
merged file is the audit's input; shard journals keep full history.

`campaign/bootstrap.sh I N [WORKERS] [BRANCH]` takes a fresh container
from a bare checkout to a running shard and is idempotent (re-run it
hourly from a Routine): toolchain at the pinned commits with self-tests;
resume from origin's shard branch if it exists, else create it; seed the
shard journal from the live journal, the branch's last checkpoint, or
the base snapshot (complete lines only); push once *before* any work so
a container without push access aborts immediately; hourly checkpoint
(gzip under the journal's flock, commit, push with rebase retry), a
checkpoint on exit, a trap for TERM/INT/HUP; if the driver is already
running, checkpoint only.  `campaign/supervise.sh` + `driver.cmd` do the
same for this container's unsharded journal (an hourly Routine runs it;
the container rebooted once and lost every process while the disk
survived).

Review: the sharding path was adversarially reviewed (4 lenses, 3
skeptics per finding, critic pass) before any container was spawned; the
14 confirmed findings - order-dependent merge, torn lines, replacement
container re-seeding and failing to push, missing push preflight /
trap / checkpoint mutual exclusion, no relaunch after a shard reboot -
are all addressed above.  Non-terminal `cake_fail` / `check_timeout`
records (e.g. a cake_lpr killed for memory) are re-attempted on every
resume (`--retry-status error,cake_fail,check_timeout`); the final
merged `--audit` reports any survivor as `bad`.
