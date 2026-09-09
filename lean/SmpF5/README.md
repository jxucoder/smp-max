# The Lean development: f(5) = 16 and f(6) = 48

Lake package `SmpF5` (the name predates the order-6 work and is kept
because CI, the papers and the import lines cite it). Lean 4 `v4.33.1`
with Mathlib (`lake exe cache get` fetches the prebuilt cache, about 8 GB
under `.lake/`). `lake build` runs 893 jobs and kernel-checks every
theorem; `grep -rn sorry SmpF5/` is empty. Sizes and theorem counts per
layer: `STATUS.md` ("Numbers behind the ledger").

## The two headline theorems

Both rest on the axioms `propext`, `Classical.choice`, `Quot.sound` and
nothing else; both have exactly one hypothesis, discharged outside the
kernel by cake_lpr-checked UNSAT certificates for formulas printed from
the Lean definitions by the exporters below.

`SmpF5/Lower.lean`:

```lean
theorem f5_eq_16_of_unsat
    (H : ∀ row ∈ perms120, ¬ Satisfiable (cubeCNF row)) :
    (∀ I : Inst, WF I = true → stableCount I ≤ 16) ∧
    (∃ I : Inst, WF I = true ∧ stableCount I = 16)
```

`SmpF5/Bridge6.lean`:

```lean
theorem f6_eq_48_of_unsat
    (H : ∀ c ∈ Cubes6.finalCubes, ¬ Satisfiable (Cubes6.cubeFormula 49 c)) :
    (∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48) ∧
    (∃ I : Inst6, WF6 I = true ∧ stableCount6 I = 48)
```

The definitions the statements quantify over are the one human-checked
step: `Inst`, `WF`, `isStable`, `stableCount` at the top of
`SmpF5/Faithful.lean` (order 5) and `Inst6`, `WF6`, `isStable6`, `sms6`,
`stableCount6` at the top of `SmpF5/SixBridge.lean` (order 6), about
forty lines each. `perms120` and `cubeCNF` (`Encoding.lean`), and
`Cubes6.finalCubes` and `Cubes6.cubeFormula` (`Cubes6.lean`,
`SplitList6.lean`), are Lean definitions; the identity between what they
print and what the certificate campaigns refuted is documented in
`VERIFYING.md` and, for order 6, `f6/campaign/lean_identity.txt`.

## Module map

All modules live in `SmpF5/`; `SmpF5.lean` imports all 37 of them. The
tables list each layer in import order (a module depends only on modules
above it and on Mathlib). Every module has a `/-! # ... -/` header
docstring that is more detailed than the line here; the faithfulness
files cite the section and lemma numbers of the archived plan
`docs/history/f6-FAITHFULNESS_PLAN.md`.

### Order-5 core

| module | what it proves |
|---|---|
| `Faithful` | Defines 5 × 5 instances as rank tables (`Inst`, `WF`), stability (`isStable`) and the count (`stableCount`); proves the covering step `cube_covering` (man 1's ranking is one of the 120 permutations). |
| `Symmetry` | `relabel I` renames women by man 0's rank row; well-formedness is preserved and the count unchanged, giving `reduce_man0'` (WLOG man 0 ranks the identity). |
| `Encoding` | `cubeCNF row`, the selector-style cube formula for order 5 at 17 slots (`cubeCNF16` at 16 for the positive control), and `Satisfiable`; the single source of truth for what `export_cnf` prints. |
| `Faithfulness` | The assignment `tau I idxs` read off an instance and its stable matchings, the literal-evaluation lemmas, and `cube_faithful'`: an instance in cube `row` with at least 17 stable matchings satisfies `cubeCNF row`. |
| `Bridge` | `f5_upper_of_unsat`: combines `reduce_man0'`, `cube_covering` and `cube_faithful` into f(5) ≤ 16 conditional on the 120 refutations. |
| `Lower` | The 16-matching witness `witnessI`, its count by kernel `decide` (via `List.permutations'`), and the combined statement `f5_eq_16_of_unsat`. |
| `../Witness.lean` | Standalone file outside the package: the same witness recounted with no imports, axiom `propext` only (`lake env lean ../Witness.lean`). |

### Order-6 reduction (11 files)

From "every well-formed order-6 instance" to "some legal schedule's
read-off instance, encoded as a fixed CNF". End statement:
`validity_unconditional` (`WRelabel6`).

| module | what it proves |
|---|---|
| `SixBridge` | Defines order-6 instances, stability and the count (`Inst6`, `WF6`, `isStable6`, `sms6`, `stableCount6`); `readoff I` promotes stable partners to the top of each list; the bridge lemma `bridge : stableCount6 I ≤ stableCount6 (readoff I)`. |
| `Lattice6` | The stable-matching lattice: `meetM I μ ν` (each man's better partner) is again stable; the man-optimal and woman-optimal matchings; the inverse-permutation toolkit `invMatch`. |
| `Chain6` | `theChain I`, an explicit maximal chain from `manOpt I` to `womanOpt I` by minimum-rank-sum dominators; `chain_complete`, `traj_mem_iff`, `wtraj_nodup`, `total_moves_le_30`: the trajectories are exactly the stable partners in preference order, without repetition, within the 30-move budget. |
| `Sym6` | Relabeling men and women by the same permutation preserves the identity matching, maps schedules to schedules and leaves `stableCount6` invariant (Lemma sym (ii)). |
| `Sched6` | Schedules as lists of cyclic steps applied from the identity matching; trajectories as destuttered partner columns; the read-off instance `readoffS` (women's trajectories reversed, canonical bottom completion) and legality `Legal`. |
| `AbsBridge6` | `count_le_of_orderPreserving`: the bridge lemma in bottom-agnostic form, for any instance ranking stable partners on top in the original order. |
| `Cycle6` | Cycle structure of one matching step: `prevOwner` is injective, so a moved man's orbit returns within six steps (makes fuel-6 orbit extraction total and correct). |
| `ChainSched6` | `chainSched I` concatenates the single-step decompositions of consecutive chain elements into one schedule whose matching sequence passes through the whole chain: the executable Validity Lemma. |
| `ValidityBridge6` | `sc_le_readoffS_chainSched`: `stableCount6 I ≤ stableCount6 (readoffS (chainSched I))` when the man-optimal matching is the identity, via the bottom-agnostic bridge. |
| `WRelabel6` | Women-only relabeling `wrelabel6` sends the man-optimal matching to the identity (`manOpt_wrelabel6`) without changing the count; hence `validity_unconditional`: every well-formed order-6 instance is dominated by the read-off of some `Legal` schedule. |
| `SchedCNF6` | The schedule CNF `schedCNF k` (and `schedCNFn n k`, `cubeCNF k prefix`), a line-by-line transcription of `f6/sched_sat.py :: build(6, k)` with the Python variable numbering; the single source of truth for what `export_sched_cnf` prints. |

### Order-6 faithfulness (19 files plus the data file `SplitList6`)

From "some legal schedule reads off at least 49 stable matchings" to "some
cube of `finalCubes` has a satisfiable formula". Chain in `Bridge6`:
`exists_canonical_schedule` → `fits_final` → `cube_faithful6`.

| module | what it proves |
|---|---|
| `Cubes6` | Campaign cubes as prefixes of min-first shapes plus a `stopped` flag; `canonicalCubes2` (the driver's `root_cubes(2)`), `extendCanon` (its `split_children`), the first-appearance rule `canonAtB`, the legality filter `legalPrefixB`; `CubeWF`, `Fits`, `cubeFormula`. Computable, so `export_cubes6` can print them. |
| `Decode6` | `dec6 k v` inverts the variable numbering of `SchedCNF6`; the decode lemmas `dec_*` (`SchedCNF6.dec_pwVar3` is the last) return each offset function's arguments. |
| `DestutterPrefix6` | Position lemmas connecting a partner column's prefixes (what the visited masks read) with first-occurrence positions in its destuttered trajectory (what the read-off ranks read). |
| `Shapes6` | Rotating a step to min-first form (`minFirst`) changes neither the matching sequence nor legality (`Legal_map_minFirst`); every legal step is an entry of `cyclicShapes 6` (`minFirst_mem_cyclicShapes`); `permsN6_perm_permutations` relates the formula's 720 matchings to Mathlib's permutations. |
| `Frames6` | The CNF state at frame `t` (`frame S t`, visited mask `vis`) and the witness assignment `tau6 k S idxs` / `τV`, which assigns every decoded variable by the gate formula the Python encoder uses for it. |
| `ReadoffSem6` | The crux `PM_sem` / `PW_sem`: under `τV` the men's and women's preference variables are true exactly when the read-off row orders the two partners that way. |
| `SchedLen6` | `Legal_length_le_15`: a legal order-6 schedule has at most 15 steps (the frame bound that fixes the formula's size); the per-man cap and the 30-move budget checked by the driver. |
| `RelabelSched6` | `relabelSched σ S` renames the men of every step; equivariance, `Legal_relabel`, and the count bridge `sc_le_readoffS_relabelSched`, re-instantiated at the relabeled instance because `readoffS` is not relabel-equivariant (plan L3.1–L3.7, L3.12–L3.16). |
| `FirstApp6` | First-appearance normalization: `partOrder`, `sigmaOf`, and `firstApp_relabel`: under `sigmaOf S` every step of `S` is first-appearance canonical; rotation invariance of `canonAtB` (plan L3.8–L3.11, L3.21, L4.14). |
| `PrefixLegal6` | Prefixes of legal schedules are legal (`Legal_take`) and pass the driver's cube filter (`legalPrefixB_of_Legal`); matching sequences and trajectories of a prefix are prefixes (plan L5.10–L5.12). |
| `FamState6` | Clause families 1–3 hold under `tau6`: `init_sat`, `matching_sat`, `step_sat` (initial state, matching one-hot, step one-hot). |
| `FamGates6` | Clause families 5–9, the definitional gates, hold under `tau6` for every schedule: `before_sat`, `neither_sat`, `pm_sat`, `beforeW_sat`, `pw_sat`, via generic gate lemmas on the exact literal patterns of `SchedCNF6`. |
| `FamTrans6` | Clause family 4, the transition clauses, holds for a legal schedule: `stopTrans_sat`, `shapeClauses_sat`, `noRevisit_sat` (from `noRevisit_sem`, plan L5.9), `visUpdate_sat`, assembled as `transition_sat`. |
| `FamSelect6` | Clause families 10–12 hold: `selector_sat`, `ladder_sat` (strictly increasing selections), `block_sat6` (a selected matching admits no blocking pair, via `PM_sem` / `PW_sem`); the index list `idxsOf` of a read-off's stable matchings and `stableCount6_eq_filter_permsN`. |
| `Units6` | The cube's unit clauses hold under the witness assignment: `prefixUnits_sat`, `stopUnits_sat`; `cubeFormula_sat_of` packages base formula plus units. |
| `Lower6` | The dihedral Latin instance `dihedral6` (OEIS A351413) and `dihedral6_count : stableCount6 dihedral6 = 48` by kernel `decide` over the 720 permutations; `f6_lower`. |
| `SplitList6` | Data generated from the journal: the ids of the depth-2 and depth-3 cubes the campaign split (`isSplitDepth2`, `isSplitDepth3`) and `finalCubes := refineCubes (refineCubes canonicalCubes2 isSplitDepth2) isSplitDepth3`, the certified cube set (numbers: `STATUS.md`). |
| `Coverage6` | Every legal first-appearance canonical schedule fits a well-formed cube of `finalCubes` (`fits_final`), from `cube_of_canonical` (a root cube fits), `fits_refine` (fitting survives a split round, for any split predicate) and the `*_WF` lemmas (plan L3.17–L3.20). |
| `Faithfulness6` | `schedCNF_sat` (the twelve family lemmas assembled), `cube_faithful6` (a legal schedule of at most 15 steps whose read-off has at least 49 stable matchings makes every fitting well-formed cube satisfiable at target 49), `exists_canonical_schedule` (from `49 ≤ stableCount6 I` to such a schedule, via `validity_unconditional`, `sigmaOf` and the count chain) and `f6_upper_of_unsat_of_coverage`. |
| `Bridge6` | `f6_upper_of_unsat` (coverage discharged by `fits_final`) and `f6_eq_48_of_unsat` (adds `f6_lower`). |

### The 1 + 25 theorems CI checks

`.github/workflows/lean-verify.yml` prints the axioms of
`f5_eq_16_of_unsat` and of 25 order-6 theorems and requires
`[propext, Classical.choice, Quot.sound]` for each; `VERIFYING.md`
("The 25 theorems CI checks") explains what each one says. By file:
`bridge` (SixBridge); `chain_complete`, `traj_mem_iff`, `wtraj_nodup`,
`total_moves_le_30` (Lattice6, Chain6); `count_le_of_orderPreserving`
(AbsBridge6); `sc_le_readoffS_chainSched` (ValidityBridge6);
`manOpt_wrelabel6`, `validity_unconditional` (WRelabel6); `PM_sem`,
`PW_sem` (ReadoffSem6); `Legal_length_le_15` (SchedLen6);
`minFirst_mem_cyclicShapes`, `permsN6_perm_permutations`,
`Legal_map_minFirst` (Shapes6); `SchedCNF6.dec_pwVar3` (Decode6);
`firstApp_relabel` (FirstApp6); `Legal_relabel`,
`sc_le_readoffS_relabelSched` (RelabelSched6);
`exists_canonical_schedule`, `cube_faithful6` (Faithfulness6);
`fits_final` (Coverage6); `dihedral6_count` (Lower6);
`f6_upper_of_unsat`, `f6_eq_48_of_unsat` (Bridge6). CI also checks that
`../Witness.lean` depends on `[propext]` alone.

## Exporters

Three executables, declared in `lakefile.toml`, print DIMACS and cube
ids from the definitions above. They are the only bridge between the
theorem statements and the files the solvers and cake_lpr saw; the
printed output is what the identity checks compare against.

| executable | source | command |
|---|---|---|
| `export_cnf` | `ExportCnf.lean` (order 5) | `lake build export_cnf`, then run `.lake/build/bin/export_cnf` in an empty directory: writes `perms120.txt`, the 120 production cubes `cubeL000.cnf` … `cubeL119.cnf` (`cubeCNF row`, 17 slots) and the 120 positive controls `cubeL16_000.cnf` … `cubeL16_119.cnf` (`cubeCNF16 row`, 16 slots). |
| `export_sched_cnf` | `ExportSchedCnf.lean` (order 6) | `export_sched_cnf OUT [--n=N] [--k=K] [--prefix=a,b;c,d,e] [--stop]`: the base formula `schedCNFn N K` (defaults N = 6, K = 49, i.e. `schedCNF49`), or the cube formula for a prefix in the driver's id syntax; `--stop` closes the cube. Examples: open cube `0,1;2,3` is `--prefix='0,1;2,3'`; closed cube `0,1;stop` is `--prefix='0,1' --stop`; the root cube `stop` is `--stop` alone. Quote the argument (the ids contain semicolons). |
| `export_cubes6` | `ExportCubes6.lean` (order 6) | `export_cubes6 OUT` prints the ids of `canonicalCubes2` (the root cubes); `--parents=FILE` prints `parent<TAB>child` for every `extendCanon` child of each id in FILE; `--final` prints the ids of `finalCubes` (the certified leaves); `--units=FILE` prints each id's unit clauses (`prefixUnits` then `stopUnits`, DIMACS lines joined by `\|`), the input of `f6/lean_rehash.py`. |

Build all three with `lake build export_cnf export_sched_cnf export_cubes6`;
binaries land in `.lake/build/bin/`. The full identity-check recipe
(what to compare with the journal, expected line counts and hashes) is in
`VERIFYING.md`; the recorded run is `f6/campaign/lean_identity.txt`.

## Build, axiom and kernel-replay commands

From this directory (`lean/SmpF5`):

```bash
lake exe cache get          # prebuilt Mathlib
lake build                  # 893 jobs; kernel-checks every theorem
! grep -rn sorry SmpF5/     # must print nothing

printf 'import SmpF5.Lower\n#print axioms f5_eq_16_of_unsat\n' > /tmp/ax5.lean
lake env lean /tmp/ax5.lean
# 'f5_eq_16_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]

printf 'import SmpF5.Bridge6\n#print axioms f6_eq_48_of_unsat\n#check @f6_eq_48_of_unsat\n' > /tmp/ax6.lean
lake env lean /tmp/ax6.lean
# 'f6_eq_48_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
# followed by the statement shown above

lake env lean ../Witness.lean
# 'witness_has_16_stable_matchings' depends on axioms: [propext]
```

The full CI axiom list (the 25 order-6 theorems) is the `Axiom check (f6
reduction layer)` step of `.github/workflows/lean-verify.yml`; paste its
`printf` line to reproduce it.

Kernel replay with Lean's built-in `leanchecker` (every declaration of
every module re-checked by the kernel; silent exit 0 per module, about
8 s each; the recorded run of 2026-09-09 is
`f6/campaign/leanchecker_2026-09-09.txt`, 38 / 38 clean):

```bash
for m in $(grep -oE '^import SmpF5\.\w+' SmpF5.lean | sed 's/import //') SmpF5; do
  lake env leanchecker $m || echo FAIL $m
done
```

## Not part of the build

`../attic/` holds two files that are neither imported by `SmpF5.lean` nor
built by `lake build`: `LratPilot.lean`, the n = 4 pilot that imported an
LRAT certificate through Mathlib's `lrat_proof` before the project
settled on the external checker cake_lpr, and `DiffTest.lean`, a
differential test of the order-5 Lean definitions against the Python
counter. See `../attic/README.md`. `../gen_witness.py` generates
`../Witness.lean` from the recorded order-5 instance.
