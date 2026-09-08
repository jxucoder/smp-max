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

Confirm no hidden holes and the exact axiom base of the main theorem
(upper and lower bound combined):

```bash
echo 'import SmpF5.Lower
#print axioms f5_eq_16_of_unsat' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```

Expected output (nothing else):

```
'f5_eq_16_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Also check the lower-bound witness (standalone, kernel-only):

```bash
lake env lean ../Witness.lean     # prints: depends on axioms: [propext]
```

`grep -rn sorry SmpF5/` must return nothing.

What this buys you: **IF the 120 cube formulas are unsatisfiable THEN
f(5) = 16** (`f5_eq_16_of_unsat`: the upper bound for every well-formed
instance AND an embedded witness with exactly 16, in one statement over
one `stableCount`), as a machine-checked theorem over the definitions
you read in item 3 above. `Witness.lean` re-proves the witness count
standalone using only `propext`.

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
  solver configs live in the results log of the root `README.md`.

## Verifying the f(6) reduction layer (Lean, ~5 min on top of Step 1)

The same `lake build` also kernel-checks the f(6)=48 reduction lemmas
(`SmpF5/SixBridge.lean`, `SmpF5/Lattice6.lean`, `SmpF5/Chain6.lean`).
Check their axiom base:

```bash
echo 'import SmpF5
#print axioms bridge
#print axioms chain_complete
#print axioms traj_mem_iff
#print axioms wtraj_nodup
#print axioms total_moves_le_30
#print axioms count_le_of_orderPreserving
#print axioms sc_le_readoffS_chainSched
#print axioms manOpt_wrelabel6
#print axioms validity_unconditional' > /tmp/ax6.lean && lake env lean /tmp/ax6.lean
```

All must report `[propext, Classical.choice, Quot.sound]`. What these
say (definitions to read: `Inst6`, `WF6`, `isStable6`, `stableCount6`,
`stab`, `readoff` at the top of `SixBridge.lean`, same style as the
order-5 ones):

- `bridge` : for well-formed order-6 `I`,
  `stableCount6 I <= stableCount6 (readoff I)` — the bridge lemma;
- `chain_complete`, `traj_*`, `wtraj_*`, `prevOwner_*` : the validity
  layer — an explicit maximal chain from the man-optimal to the
  woman-optimal stable matching whose trajectories are exactly the
  stable partners in preference order, within all schedule budgets,
  with each step decomposing into disjoint cyclic swaps (the closing
  docstring of `Chain6.lean` maps every clause to its theorem);
- `count_le_of_orderPreserving` (AbsBridge6.lean): the bridge in
  bottom-agnostic form;
- `sc_le_readoffS_chainSched` (ValidityBridge6.lean) and, unconditionally,
  **`validity_unconditional`** (WRelabel6.lean): for every well-formed
  order-6 instance `I` there is a `Legal` schedule `S` with
  `stableCount6 I <= stableCount6 (readoffS S)` — the composed Validity +
  Bridge statement; `readoffS`/`Legal` in `Sched6.lean` are the read-off
  instance and schedule legality of Definitions 1–2 (bottom completion in
  ascending label order, women's trajectories reversed, exactly as
  `gen_enum.c` builds them).

**What is NOT formalized:** the exhaustive enumeration of the schedule
space (26.6e9 nodes, C program `f6/gen_enum.c`) and the symmetry
reduction soundness of its canonicalization (validated computationally:
on/off agreement; see `f6/paper/f6.pdf` Section "Validation"). The
f(6)=48 claim = these Lean lemmas + the validated enumeration + the
dihedral lower bound (checkable in seconds: `python3 smp.py`).

## Known gaps (state of 2026-09-01)

- LRAT certificates are not archived (regenerable in ~2 h; a Zenodo
  archive with DOI is planned so verifiers can skip solving and only
  re-check).
- The f(6) enumeration has now been *replaced* by a certificate campaign
  (2026-09-08, `f6/CAMPAIGN.md` "Result"): every legal canonical
  schedule prefix is a cube of the Lean-defined formula `SchedCNF6`, all
  25,493 root cubes are refuted (318,736 cake_lpr-checked certificates
  over the split tree, journaled with per-cube CNF and LRAT hashes,
  `--audit` exit 0). What is still not machine-checked is the
  *faithfulness* theorem (that the formula encodes "read-off count
  ≥ 49"); until it lands, the f(6) trust base is the Lean reduction +
  the validated encoding + cake_lpr, not a single Lean theorem as for
  f(5).
