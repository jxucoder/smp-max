# Verifying the results

All commands below start at the repository root unless stated otherwise.
These checks establish different parts of the [evidence chain](results.md).

| Check | Prerequisites | Cost and expected outcome |
|---|---|---|
| Saved witnesses | Python 3.9+, standard library | Seconds to a minute depending on hardware; counts 16, 48, 85, 85 |
| Lean statements and axioms | elan; pinned Lean/Mathlib | Initial cache can use several GB; initial build typically minutes to tens of minutes |
| Artifact checksums | Python standard library | Reads retained artifacts; all SHA-256 values match |
| Recorded campaign audit | Python; decompressed journal | Approximately 464 MB journal plus several GB of working memory; complete coverage and recorded verdict fields |
| Fresh f(5) certificates | Lean exporter, kissat, drat-trim, cake_lpr | Historical estimate: 2–3 hours serial; allow several GB of scratch space |
| Fresh f(6) certificates | Schedule exporter/driver, CaDiCaL, cake_lpr | A full run is substantial: historical solver time alone was about 299 core-hours, plus checking/I/O; total proof output was about 20 TB streamed through deletion |

Historical timings are guides, not guarantees. Journal auditing does not
recheck the deleted certificates. A fresh certificate run verifies the
UNSAT evidence, but does not finish the missing order-6 Lean theorem.

## 1. Obtain the repository and tools

```bash
git clone https://github.com/jxucoder/smp-max.git
cd smp-max
```

Install [elan](https://github.com/leanprover/elan) using its installation
instructions, then fetch the pinned Mathlib cache:

```bash
(cd lean && lake exe cache get)
```

[lean-toolchain](../lean/lean-toolchain) pins Lean 4 v4.33.1;
[lake-manifest.json](../lean/lake-manifest.json) pins all Lean dependencies.
Python-only witness and journal checks do not require Lean or PySAT.
PySAT is needed only for the [direct-encoding experiments](../experiments/README.md).

## 2. Check the explicit witnesses

```bash
python3 tools/verify_witnesses.py
```

Expected: four `[OK]` rows and `Verified 4 witnesses.` The program checks
preference permutations, compares full matching sets, and checks
rotation-poset downsets. Each saved order-7 schedule is also checked against
its preference data. Any failure exits nonzero.

`python3 tools/stable_matchings.py` is a separate sanity check against
Latin instances with counts 3, 10, 9, and 48. Its order-5 example is not
the extremal instance.

## 3. Check Lean and inspect the definitions

```bash
bash tools/check_lean.sh
```

The script builds the library and all three exporters, checks for `sorry`,
checks the 17 established theorem axiom sets, checks the standalone
order-5 witness, runs the differential count check, and checks the
order-4 LRAT pilot. Success ends with a summary of the passed checks.

Read the definitions in [Five/Definitions.lean](../lean/SmpMax/Five/Definitions.lean)
and [Six/ReadOff.lean](../lean/SmpMax/Six/ReadOff.lean): `Inst`, `WF`,
`isStable`, and `stableCount`, with their order-6 counterparts. These
must express the intended mathematical problem. The [module map](../lean/README.md)
links the reduction and encoding statements.

The main theorem `f5_eq_16_of_unsat` depends only on `propext`,
`Classical.choice`, and `Quot.sound`. Its 120 UNSAT hypotheses are
discharged outside Lean. The standalone witness depends only on `propext`.

## 4. Check retained artifacts and recorded campaign coverage

```bash
python3 tools/check_artifacts.py
mkdir -p runs/f6
gzip -dc results/f6/campaign-2026-09-08/campaign.jsonl.gz > runs/f6/campaign.jsonl
python3 -m tools.campaign.cube_campaign --audit --journal runs/f6/campaign.jsonl
```

The final coverage line must contain:

```text
roots=25493 nodes=321492 verified=318736 missing=0 bad=0
```

The audit ends with `audit: OK` and exit 0. A source-hash provenance
notice may report that the encoder source changed since the historical
header; the reorganization changed imports/documentation but preserved
the formula. Formula identity is checked independently. See the
[layout comparison](layout-verification.md).

This audit checks recorded coverage and verdict fields, not LRAT proof
contents. All completed-run evidence is retained under
[results/f6/campaign-2026-09-08](../results/f6/campaign-2026-09-08/README.md).

## 5. Regenerate and check the order-5 certificates

Build [kissat](https://github.com/arminbiere/kissat),
[drat-trim](https://github.com/marijnheule/drat-trim), and
[cake_lpr](https://github.com/tanyongkiam/cake_lpr) from their upstream
sources. The recorded run used kissat 4.0.4, drat-trim `2e3b2dc`, and
cake_lpr `a36874a`. Build a checker appropriate for your platform and run
its self-test. The [campaign reference](reference/campaign.md) records the
order-6 native-LRAT toolchain separately.

Place kissat on PATH and the other two executables at `dt-src/drat-trim`
and `cake_lpr-src/cake_lpr`, or pass their paths through the runner's
`--kissat`, `--drat-trim`, and `--cake-lpr` options.

```bash
python3 tools/verify_five_cubes.py --export-only
python3 tools/verify_five_cubes.py
```

The first command exports the formulas from Lean into `runs/f5/lean-cubes/`.
The second regenerates them, solves all 120 upper-bound cubes, converts
DRAT to LRAT, and checks each LRAT. Expected final output:
`Verified 120/120 cubes in this run. All upper-bound cubes checked.`

The runner explicitly accepts solver exit 20, requires checker success,
records formula/proof hashes, and stops on failure with artifacts retained.
Successful DRAT/LRAT files are removed after recording verification; use
`--keep-proofs` to retain them. `--cubes 0 1` checks only a subset and is
insufficient to establish the upper bound.

For comparison, concatenate the 120 upper-bound CNFs in zero-padded cube
order: their SHA-256 is
`044d0edbd9762166d925038056b3ef9ed762293d3f7637055e1105d1eca30ec6`.
The historical `a93f5e58…` hash covers **all 240** CNFs, including the
positive controls; the old `cubeL*.cnf` glob selected both sets.
`cubeL16_105.cnf` is the positive control containing the known witness
and should be SAT (solver exit 10).

## 6. Regenerate order-6 formulas or certificates

```bash
mkdir -p runs/f6
lean/.lake/build/bin/export_sched_cnf runs/f6/base.cnf
lean/.lake/build/bin/export_sched_cnf runs/f6/example.cnf '--prefix=0,1;2,3'
lean/.lake/build/bin/export_sched_cnf runs/f6/stopped.cnf '--prefix=0,1' --stop
```

The base must have 84,882 variables and 2,709,212 clauses. Its SHA-256
is recorded in the [campaign summary](../results/f6/campaign-2026-09-08/summary.json).
Shell-quote cube prefixes because semicolons have shell meaning.

Follow the [campaign reference](reference/campaign.md) to solve/check a
sample cube or launch a full regeneration. The original LRAT files are
not available; their journaled hashes identify historical files and a new
solver run need not reproduce the same proof bytes. The regenerated CNF
must match the corresponding journaled CNF hash.

`--expect-cnf-dir` rehashes Python-generated cube formulas and optionally
compares preexisting external files. It does not run Lean automatically.
The reference explains the required external filenames and coverage limits.
