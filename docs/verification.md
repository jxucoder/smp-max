# Verification guide

Run the commands below from the repository root. The checks progress from
saved witnesses to formal statements, formula identity, and freshly checked
SAT certificates. The [evidence ledger](results.md) records the original runs.

| Check | Establishes | Typical cost |
|---|---|---|
| Witness recount | Lower bounds 16, 48, 85 and 85 | Seconds |
| Lean build and axioms | Both exact-maximum theorems, conditional on UNSAT | Initial dependency download and build: about 20–30 minutes |
| Campaign identity and audit | Complete cube coverage and every recorded formula hash | A few minutes after building |
| Order-5 certificates | Independently checks all 120 upper-bound cubes | About 2–3 hours |
| Order-6 certificates | Independently checks selected or all upper-bound cubes | Minutes for the 205-cube sample; about 300 core-hours for the full tree |

## Prerequisites

- macOS or Linux, Python 3.9 or later, and Git.
- [elan](https://github.com/leanprover/elan) for Lean. The toolchain and
  Mathlib versions are pinned in `lean/`; allow roughly 8 GB for dependencies.
- Solvers and cake_lpr only for certificate regeneration. See the
  [pinned toolchain instructions](reference/solver-toolchain.md).

The verification tools use the Python standard library. Alternative
experiments requiring PySAT use `requirements-experiments.txt`.
Generated output goes under the ignored `runs/` directory.

## 1. Check witnesses and saved files

```bash
python3 tools/verify_witnesses.py
python3 tools/check_artifacts.py
python3 tools/check_docs.py
```

Expected witness counts: **16, 48, 85, 85**. The verifier compares complete
matching sets from two counters, checks rotation-poset downset counts, and
reconstructs the order-7 preferences from their schedules. These establish
lower bounds. Artifact hashes establish file identity, not mathematical validity.

## 2. Build and inspect the Lean statements

```bash
(cd lean && lake exe cache get)
bash tools/check_lean.sh
```

This builds the library and all three exporters, rejects `sorry`, and checks
26 theorem axiom lists, including `f5_eq_16_of_unsat` and `f6_eq_48_of_unsat`.
Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`. It also
checks the standalone order-5 witness (only `propext`), 300 differential
count cases (zero mismatches), and the order-4 LRAT pilot.

The statements have the same shape: if all specified Lean-defined CNFs
are unsatisfiable, the maximum is exactly 16 or 48. For order 5 there are
120 formulas; for order 6 there are 318,736 leaf formulas. The order-6
normalization, encoding faithfulness and cube coverage proofs are complete.
The [Lean guide](../lean/README.md) gives the statements and reading order.

Read the definitions of instances, well-formedness, stability and counting
in [Five/Definitions.lean](../lean/SmpMax/Five/Definitions.lean) and
[Six/ReadOff.lean](../lean/SmpMax/Six/ReadOff.lean) to confirm that the
formal statements express the intended stable-marriage problem.

Optional kernel replay of every imported module, from the repository root:

```bash
cd lean
python3 - <<'PY'
from pathlib import Path
import subprocess
modules = [line.split()[1] for line in Path('SmpMax.lean').read_text().splitlines()
           if line.startswith('import SmpMax.')]
for module in [*modules, 'SmpMax']:
    subprocess.run(['lake', 'env', 'leanchecker', module], check=True)
print(f'{len(modules) + 1} modules replayed successfully')
PY
```

## 3. Audit the campaign and check every formula

```bash
mkdir -p runs/f6
gzip -dc results/f6/campaign-2026-09-08/campaign.jsonl.gz > runs/f6/campaign.jsonl
python3 tools/campaign/check_lean_identity.py --journal runs/f6/campaign.jsonl
```

The helper invokes the current Lean exporters and compares their output
with the journal and Python cube definitions. Every mismatch causes failure.
Expected results:

- Audit: **321,492** distinct cubes, **318,736** verified, **2,756** split;
  zero missing or bad records and `audit: OK`.
- Exactly **25,493** roots and **295,999** children of the recorded splits.
- `Cubes6.finalCubes`: **318,736** unique IDs, equal to the verified set.
- All **321,492** recorded formula hashes match; zero missing unit lists.

The base CNF hash is
`28421fb68b0f494b99d1918aa64cff248443161dc7a6c220e0c3e895a67df59b`.
Outputs, complete ID lists and a JSON summary are in `runs/f6/lean-identity/`.
For the low-level recipe, see the exporters in the [Lean guide](../lean/README.md).
The original [identity transcript](../results/f6/campaign-2026-09-08/lean_identity.txt)
uses historical paths; the [migration map](path-migration.md) resolves them.

Source hashes in the journal identify the original scripts. Moving imports
and changing documentation changes a source hash without changing the
formula. The audit reports that difference as provenance; formula mismatch
is a failure. The full identity check above independently checks the formulas.

## 4. Regenerate the order-5 certificates

Install kissat 4.0.4 on `PATH`, drat-trim (historical commit `2e3b2dc`) at
`dt-src/drat-trim`, and cake_lpr at `cake_lpr-src/cake_lpr`. The
[toolchain reference](reference/solver-toolchain.md) covers cake_lpr;
the other sources are [kissat](https://github.com/arminbiere/kissat) and
[drat-trim](https://github.com/marijnheule/drat-trim).

```bash
python3 tools/verify_five_cubes.py
```

The runner exports the Lean formulas, requires solver exit 20 (UNSAT),
checks DRAT and LRAT verdicts, and records formula/proof hashes before
deleting successful proof files. Failures stop the run and retain artifacts.
Use `--keep-proofs` to archive certificates. A successful full run ends
with `Verified 120/120 cubes in this run. All upper-bound cubes checked.`

To inspect formulas without solving:

```bash
python3 tools/verify_five_cubes.py --export-only
```

Files go to `runs/f5/lean-cubes/`: 120 production CNFs, 120 positive
controls and `perms120.txt`. Concatenated in filename order, the production
CNFs hash to `044d0edbd9762166d925038056b3ef9ed762293d3f7637055e1105d1eca30ec6`;
all 240 hash to `a93f5e58cd23976b303e26f5dd2fcd4ab66f91797b0b02bd2bfba13887c6a2ef`.
The positive control `cubeL16_105.cnf` must be SAT.

## 5. Regenerate order-6 certificates

Follow [solver setup and sample re-solving](reference/solver-toolchain.md).
It includes a positive control and the exact 205-cube sample recorded in
the repository. For each re-solved cube, require a valid checker verdict
and the same CNF hash. A different proof hash can reflect a different solver
build; it still needs independent acceptance by the checker.

The [campaign reference](reference/campaign.md) covers a complete run.
Use the verified ID list produced in step 3 to reproduce the existing
leaf set. A sample does not discharge the full UNSAT hypothesis.

## What remains trusted

The formal side relies on Lean's kernel, the three listed axioms, and the
human interpretation of the problem definitions. The certificate side
relies on the DIMACS printers, formula identity, a sound LRAT checker and
its execution environment. The solvers supply certificates to that checker.

The stored order-6 journal is self-attested: it records the driver's
transcription of checker verdicts. About 25 TB of certificates were deleted.
Auditing the journal and recomputing hashes do not re-check those certificates;
fresh solving and checking are required for independent verification.
The saved 205-cube second-machine check does not cover the whole tree.
Order-5 certificates were also not archived and can be regenerated in step 4.
