# f(5) = 16

**What it rests on.** `f5_eq_16_of_unsat` (`../lean/SmpF5/SmpF5/Lower.lean`)
is one Lean 4 theorem, zero sorries, axioms `propext`, `Classical.choice`,
`Quot.sound`:

    (∀ row ∈ perms120, ¬Satisfiable (cubeCNF row)) →
      (∀ I : Inst, WF I = true → stableCount I ≤ 16) ∧ ∃ I, WF I = true ∧ stableCount I = 16

Its only hypothesis is discharged by 120 cake_lpr-checked certificates for
the 120 cube formulas printed from the Lean definitions
(`../lean/SmpF5/ExportCnf.lean`); the witness is also a kernel-only theorem
(`../lean/Witness.lean`, axiom `propext`). Ledger: `../STATUS.md`; recipe
(2 to 3 hours unattended): `../VERIFYING.md`. The Lean development lives in
`../lean/` (package `SmpF5`, which also hosts the order-6 files); this
directory holds the solver-side runs and the paper.

## What is in this directory

| path | role |
|---|---|
| `cubesL/cubesL_results.txt` | **the log the theorem cites**: for each of the 120 Lean-exported cubes `cubeL000..119`, kissat UNSAT, drat-trim verified, cake_lpr `s VERIFIED UNSAT` |
| `cubesL/run_one.sh` | the per-cube loop behind that log (run from `cubesL/`; tools in `../../dt-src`, `../../cake_lpr-src`; the `.cnf` files are gitignored, regenerate them with `export_cnf`) |
| `cakelpr_results.txt` | the earlier cake_lpr run (`cube000..119`) over the Python-exported cubes of `cube_run.py` (gitignored `cubes/`); superseded by `cubesL/`, kept as an independent refutation |
| `cube_run.py`, `cube_probe.py` | cube-and-conquer over man 1's preference order on the direct encoding: the full 120-cube production run and the 4-cube probe that sized it |
| `cube_enum.py`, `enum_results.txt` | per-cube enumeration of every canonical order-5 profile with 16 stable matchings; confirms A344669(5) (`../STATUS.md`) |
| `f4_ge11_fixman0.cnf`, `f5_ge17_fixman0.cnf`, `unsat17.log` | the direct encoding of "some n x n instance has at least k stable matchings" (`../encode.py`, man 0's list fixed) at (4, 11) and (5, 17), and the UNSAT log of the latter: the first, uncertified refutations (f(4) = 10 re-proved as a tooling check) |
| `paper/` | `f5.tex`, `f5.pdf`: the paper, including the 16-matching witness instance |
