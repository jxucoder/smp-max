# Order-6 cube campaign (`cube_campaign.py`)

Certified refutation of "some legal order-6 schedule S has sc(R(S)) >= 49"
by cube-and-conquer over canonical schedule prefixes.  Every cube emits
its own certificate chain, checked by cake_lpr, then deleted (f5-style
streaming).  See `REPLAY_DESIGN.md` for the architecture and the pilot.

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
2. `kissat -q --time=T cnf drat` (binary DRAT);
3. rc 20 -> `drat-trim cnf drat -L lrat` (require `s VERIFIED`) -> record
   `lrat_sha256` -> `cake_lpr cnf lrat` (require `s VERIFIED UNSAT`) ->
   status `verified`, delete cnf/drat/lrat;
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
`verified` record, `kissat_rc == 20`, `drattrim_verified`,
`cake_verified`, no killed flag, and well-formed `cnf_sha256` /
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
