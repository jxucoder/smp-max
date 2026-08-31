# Verifying f(5) = 16 from scratch

This guide lets a third party check every link of the evidence chain on
their own machine, **without trusting any run we performed**. Total cost:
about half an hour of reading and 2–3 hours of unattended compute.

## What you end up trusting (and nothing else)

1. **Lean 4's kernel** (small, independently re-implementable; you can
   additionally run `lean4checker`).
2. **Three standard axioms**: `propext`, `Classical.choice`, `Quot.sound`
   (`Witness.lean` needs only `propext`).
3. **~40 lines of definitions** (`Inst`, `WF`, `isStable`, `stableCount`
   in `f5/lean/SmpF5/SmpF5/Faithful.lean`) — YOU must read these and
   agree they say "5×5 stable-marriage instance" and "number of stable
   matchings". This is the one irreducibly human step.
4. **One LRAT proof checker of your choice.** We used cake_lpr, whose
   correctness is itself machine-checked down to machine code; you may
   substitute any checker (drat-trim, lrat-check, verified Coq/Lean
   checkers). Checker diversity replaces trust.
5. The ~30-line DIMACS printer `ExportCnf.lean` (read it, or bypass it by
   printing the Lean terms yourself).

Not on the list: our solver runs, our Python scripts, our honesty.

## Step 1 — check the Lean development (~20 min machine time)

```bash
git clone <this repo> && cd smp-max/f5/lean/SmpF5
lake exe cache get      # prebuilt Mathlib (or build from source if paranoid)
lake build              # kernel-checks every theorem; must end with no errors
```

Confirm no hidden holes and the exact axiom base:

```bash
echo 'import SmpF5.Bridge
#print axioms f5_upper_of_unsat' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```

Expected output (nothing else):

```
'f5_upper_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Also check the lower-bound witness (standalone, kernel-only):

```bash
lake env lean ../Witness.lean     # prints: depends on axioms: [propext]
```

`grep -rn sorry SmpF5/` must return nothing.

What this buys you: **IF the 120 cube formulas are unsatisfiable THEN
f(5) ≤ 16** (`f5_upper_of_unsat`), and **a concrete instance with exactly
16 stable matchings exists** (`Witness.lean`), both as machine-checked
theorems over the definitions you read in item 3 above.

## Step 2 — read the definitions (~30 min, human)

Read, in this order:
- `SmpF5/Faithful.lean` — `Inst`, `isRankRow`, `WF`, `isStable`,
  `stableCount` (the mathematical content, ~40 lines);
- the statement (not proof) of `f5_upper_of_unsat` in `SmpF5/Bridge.lean`;
- `SmpF5/Encoding.lean` — `cubeCNF` and `Satisfiable` (you need not
  understand the encoding; the theorem quantifies over it);
- `ExportCnf.lean` — the printer.

## Step 3 — regenerate and refute the 120 formulas (~2–3 h unattended)

```bash
lake build export_cnf
mkdir -p /tmp/cubes && cd /tmp/cubes
<repo>/f5/lean/SmpF5/.lake/build/bin/export_cnf
```

This prints the 120 DIMACS files **from the Lean definitions**. For
reference, our export hashes to

```
cat cubeL*.cnf | shasum -a 256
a93f5e58cd23976b303e26f5dd2fcd4ab66f91797b0b02bd2bfba13887c6a2ef
```

but you need not compare — you generated your own copies.

Now refute each with any DRAT/LRAT-producing solver and check each proof
with any checker you trust. Our loop (kissat 4.0.4, drat-trim @2e3b2dc,
cake_lpr @a36874a, built from their public sources):

```bash
for i in $(seq -f '%03g' 0 119); do
  kissat -q cubeL$i.cnf cubeL$i.drat            # expect exit 20 (UNSAT)
  drat-trim cubeL$i.cnf cubeL$i.drat -L cubeL$i.lrat   # expect "s VERIFIED"
  cake_lpr cubeL$i.cnf cubeL$i.lrat             # expect "s VERIFIED UNSAT"
  rm cubeL$i.drat cubeL$i.lrat                  # ~0.5GB per cube otherwise
done
```

All 120 must report UNSAT + VERIFIED. Our run's log is
`f5/cubesL/cubesL_results.txt` (sha256
`200062889de4aea7ab5e15b959fed8367dd62c6eeddac319a43d70be7c3dccb9`),
kept for reference only — your own run supersedes it.

Together with Step 1 this discharges the hypothesis of
`f5_upper_of_unsat`: **f(5) ≤ 16**, hence with the witness, **f(5) = 16**.

## Optional cross-checks

- Positive control: `cubeL16_105.cnf` (16 slots, the cube containing the
  known extremal instance) must be **SAT** — guards against encodings
  that are vacuously unsatisfiable.
- `python3 smp.py` validates the independent brute-force counter against
  four known extremal instances from OEIS A351413 (3/10/9/48).
- Independent earlier refutations of "≥17" with a different encoding and
  solver configs live in `f5/README.md` (results log).

## Known gaps (state of 2026-08-31)

- Upper and lower bounds are two theorems over two syntactically
  different (definitionally equivalent-by-construction) counts:
  `Witness.lean` enumerates via a bespoke `permsOf`, the package via
  `List.permutations`. The ~50-line enumeration-equivalence lemma that
  merges them into a single `f5 = 16` statement is pending.
- LRAT certificates are not archived (regenerable in ~2 h; a Zenodo
  archive with DOI is planned so verifiers can skip solving and only
  re-check).
