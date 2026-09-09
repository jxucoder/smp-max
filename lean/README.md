# The Lean development: f(5) = 16 and f(6) = 48

One Lake package, `SmpMax`, contains the order-5 and order-6 proofs.
Modules are grouped under `SmpMax/Five/` and `SmpMax/Six/`. Lean 4 `v4.33.1`
with Mathlib (`lake exe cache get` fetches the prebuilt cache, about 8 GB
under `.lake/`). `lake build` kernel-checks every theorem; `grep -rn sorry SmpMax/` is empty. Sizes and theorem counts per
layer: `docs/results.md` ("Numbers behind the ledger").

## The two headline theorems

Both rest on the axioms `propext`, `Classical.choice`, `Quot.sound` and
nothing else; both have exactly one hypothesis, discharged outside the
kernel by cake_lpr-checked UNSAT certificates for formulas printed from
the Lean definitions by the exporters below.

`SmpMax/Five/ExactMaximum.lean`:

```lean
theorem f5_eq_16_of_unsat
    (H : ∀ row ∈ perms120, ¬ Satisfiable (cubeCNF row)) :
    (∀ I : Inst, WF I = true → stableCount I ≤ 16) ∧
    (∃ I : Inst, WF I = true ∧ stableCount I = 16)
```

`SmpMax/Six/ExactMaximum.lean`:

```lean
theorem f6_eq_48_of_unsat
    (H : ∀ c ∈ Cubes6.finalCubes, ¬ Satisfiable (Cubes6.cubeFormula 49 c)) :
    (∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48) ∧
    (∃ I : Inst6, WF6 I = true ∧ stableCount6 I = 48)
```

The definitions the statements quantify over are the one human-checked
step: `Inst`, `WF`, `isStable`, `stableCount` at the top of
`SmpMax/Five/Definitions.lean` (order 5) and `Inst6`, `WF6`, `isStable6`, `sms6`,
`stableCount6` at the top of `SmpMax/Six/ReadOff.lean` (order 6), about
forty lines each. `perms120` and `cubeCNF` (`SmpMax/Five/Encoding.lean`), and
`Cubes6.finalCubes` and `Cubes6.cubeFormula` (`SmpMax/Six/CampaignCubes.lean`,
`SmpMax/Six/CampaignSplits.lean`), are Lean definitions; the identity between what they
print and what the certificate campaigns refuted is documented in
`docs/verification.md` and, for order 6, `results/f6/campaign-2026-09-08/lean_identity.txt`.

## Module map

All modules live in `SmpMax/`; `SmpMax.lean` imports all 37 of them. The
tables group the modules by layer; a module depends only on modules
above it and on Mathlib (the exact import order is `SmpMax.lean`). Every module has a `/-! # ... -/` header
docstring that is more detailed than the line here; the faithfulness
files cite the section and lemma numbers of the archived plan
`docs/design/f6-faithfulness.md`.

### Order-5 core

| module | what it proves |
|---|---|
| [Five/Definitions.lean](SmpMax/Five/Definitions.lean) | Defines 5 × 5 instances as rank tables (`Inst`, `WF`), stability (`isStable`) and the count (`stableCount`); proves the covering step `cube_covering` (man 1's ranking is one of the 120 permutations). |
| [Five/Symmetry.lean](SmpMax/Five/Symmetry.lean) | `relabel I` renames women by man 0's rank row; well-formedness is preserved and the count unchanged, giving `reduce_man0'` (WLOG man 0 ranks the identity). |
| [Five/Encoding.lean](SmpMax/Five/Encoding.lean) | `cubeCNF row`, the selector-style cube formula for order 5 at 17 slots (`cubeCNF16` at 16 for the positive control), and `Satisfiable`; the single source of truth for what `export_cnf` prints. |
| [Five/EncodingFaithfulness.lean](SmpMax/Five/EncodingFaithfulness.lean) | The assignment `tau I idxs` read off an instance and its stable matchings, the literal-evaluation lemmas, and `cube_faithful'`: an instance in cube `row` with at least 17 stable matchings satisfies `cubeCNF row`. |
| [Five/UpperBound.lean](SmpMax/Five/UpperBound.lean) | `f5_upper_of_unsat`: combines `reduce_man0'`, `cube_covering` and `cube_faithful` into f(5) ≤ 16 conditional on the 120 refutations. |
| [Five/ExactMaximum.lean](SmpMax/Five/ExactMaximum.lean) | The 16-matching witness `witnessI`, its count by kernel `decide` (via `List.permutations'`), and the combined statement `f5_eq_16_of_unsat`. |
| `checks/FiveWitness.lean` | Standalone file outside the package: the same witness recounted with no imports, axiom `propext` only (`lake env lean checks/FiveWitness.lean`). |

### Order-6 reduction (11 files)

From "every well-formed order-6 instance" to "some legal schedule's
read-off instance, encoded as a fixed CNF". End statement:
`validity_unconditional` (`Six/NormalizeMatching`).

| module | what it proves |
|---|---|
| [Six/ReadOff.lean](SmpMax/Six/ReadOff.lean) | Defines order-6 instances, stability and the count (`Inst6`, `WF6`, `isStable6`, `sms6`, `stableCount6`); `readoff I` promotes stable partners to the top of each list; the bridge lemma `bridge : stableCount6 I ≤ stableCount6 (readoff I)`. |
| [Six/Lattice.lean](SmpMax/Six/Lattice.lean) | The stable-matching lattice: `meetM I μ ν` (each man's better partner) is again stable; the man-optimal and woman-optimal matchings; the inverse-permutation toolkit `invMatch`. |
| [Six/Chains.lean](SmpMax/Six/Chains.lean) | `theChain I`, an explicit maximal chain from `manOpt I` to `womanOpt I` by minimum-rank-sum dominators; `chain_complete`, `traj_mem_iff`, `wtraj_nodup`, `total_moves_le_30`: the trajectories are exactly the stable partners in preference order, without repetition, within the 30-move budget. |
| [Six/Relabeling.lean](SmpMax/Six/Relabeling.lean) | Relabeling men and women by the same permutation preserves the identity matching, maps schedules to schedules and leaves `stableCount6` invariant (Lemma sym (ii)). |
| [Six/Schedule.lean](SmpMax/Six/Schedule.lean) | Schedules as lists of cyclic steps applied from the identity matching; trajectories as destuttered partner columns; the read-off instance `readoffS` (women's trajectories reversed, canonical bottom completion) and legality `Legal`. |
| [Six/OrderPreservingBridge.lean](SmpMax/Six/OrderPreservingBridge.lean) | `count_le_of_orderPreserving`: the bridge lemma in bottom-agnostic form, for any instance ranking stable partners on top in the original order. |
| [Six/CycleDecomposition.lean](SmpMax/Six/CycleDecomposition.lean) | Cycle structure of one matching step: `prevOwner` is injective, so a moved man's orbit returns within six steps (makes fuel-6 orbit extraction total and correct). |
| [Six/ChainToSchedule.lean](SmpMax/Six/ChainToSchedule.lean) | `chainSched I` concatenates the single-step decompositions of consecutive chain elements into one schedule whose matching sequence passes through the whole chain: the executable Validity Lemma. |
| [Six/ScheduleDominance.lean](SmpMax/Six/ScheduleDominance.lean) | `sc_le_readoffS_chainSched`: `stableCount6 I ≤ stableCount6 (readoffS (chainSched I))` when the man-optimal matching is the identity, via the bottom-agnostic bridge. |
| [Six/NormalizeMatching.lean](SmpMax/Six/NormalizeMatching.lean) | Women-only relabeling `wrelabel6` sends the man-optimal matching to the identity (`manOpt_wrelabel6`) without changing the count; hence `validity_unconditional`: every well-formed order-6 instance is dominated by the read-off of some `Legal` schedule. |
| [Six/ScheduleEncoding.lean](SmpMax/Six/ScheduleEncoding.lean) | The schedule CNF `schedCNF k` (and `schedCNFn n k`, `cubeCNF k prefix`), a line-by-line transcription of `tools/schedule_encoding.py :: build(6, k)` with the Python variable numbering; the single source of truth for what `export_sched_cnf` prints. |

### Order-6 faithfulness (19 files plus the data file `Six/CampaignSplits`)

From "some legal schedule reads off at least 49 stable matchings" to "some
cube of `finalCubes` has a satisfiable formula". Chain in `Six/ExactMaximum`:
`exists_canonical_schedule` → `fits_final` → `cube_faithful6`.

| module | what it proves |
|---|---|
| [Six/CampaignCubes.lean](SmpMax/Six/CampaignCubes.lean) | Campaign cubes as prefixes of min-first shapes plus a `stopped` flag; `canonicalCubes2` (the driver's `root_cubes(2)`), `extendCanon` (its `split_children`), the first-appearance rule `canonAtB`, the legality filter `legalPrefixB`; `CubeWF`, `Fits`, `cubeFormula`. Computable, so `export_cubes6` can print them. |
| [Six/VariableDecoding.lean](SmpMax/Six/VariableDecoding.lean) | `dec6 k v` inverts the variable numbering of `Six/ScheduleEncoding`; the decode lemmas `dec_*` (`SchedCNF6.dec_pwVar3` is the last) return each offset function's arguments. |
| [Six/TrajectoryPrefixes.lean](SmpMax/Six/TrajectoryPrefixes.lean) | Position lemmas connecting a partner column's prefixes (what the visited masks read) with first-occurrence positions in its destuttered trajectory (what the read-off ranks read). |
| [Six/CyclicShapes.lean](SmpMax/Six/CyclicShapes.lean) | Rotating a step to min-first form (`minFirst`) changes neither the matching sequence nor legality (`Legal_map_minFirst`); every legal step is an entry of `cyclicShapes 6` (`minFirst_mem_cyclicShapes`); `permsN6_perm_permutations` relates the formula's 720 matchings to Mathlib's permutations. |
| [Six/FrameAssignment.lean](SmpMax/Six/FrameAssignment.lean) | The CNF state at frame `t` (`frame S t`, visited mask `vis`) and the witness assignment `tau6 k S idxs` / `τV`, which assigns every decoded variable by the gate formula the Python encoder uses for it. |
| [Six/ReadOffSemantics.lean](SmpMax/Six/ReadOffSemantics.lean) | The crux `PM_sem` / `PW_sem`: under `τV` the men's and women's preference variables are true exactly when the read-off row orders the two partners that way. |
| [Six/ScheduleLength.lean](SmpMax/Six/ScheduleLength.lean) | `Legal_length_le_15`: a legal order-6 schedule has at most 15 steps (the frame bound that fixes the formula's size); the per-man cap and the 30-move budget checked by the driver. |
| [Six/ScheduleRelabeling.lean](SmpMax/Six/ScheduleRelabeling.lean) | `relabelSched σ S` renames the men of every step; equivariance, `Legal_relabel`, and the count bridge `sc_le_readoffS_relabelSched`, re-instantiated at the relabeled instance because `readoffS` is not relabel-equivariant (plan L3.1–L3.7, L3.12–L3.16). |
| [Six/FirstAppearance.lean](SmpMax/Six/FirstAppearance.lean) | First-appearance normalization: `partOrder`, `sigmaOf`, and `firstApp_relabel`: under `sigmaOf S` every step of `S` is first-appearance canonical; rotation invariance of `canonAtB` (plan L3.8–L3.11, L3.21, L4.14). |
| [Six/PrefixLegality.lean](SmpMax/Six/PrefixLegality.lean) | Prefixes of legal schedules are legal (`Legal_take`) and pass the driver's cube filter (`legalPrefixB_of_Legal`); matching sequences and trajectories of a prefix are prefixes (plan L5.10–L5.12). |
| [Six/StateClauses.lean](SmpMax/Six/StateClauses.lean) | Clause families 1–3 hold under `tau6`: `init_sat`, `matching_sat`, `step_sat` (initial state, matching one-hot, step one-hot). |
| [Six/GateClauses.lean](SmpMax/Six/GateClauses.lean) | Clause families 5–9, the definitional gates, hold under `tau6` for every schedule: `before_sat`, `neither_sat`, `pm_sat`, `beforeW_sat`, `pw_sat`, via generic gate lemmas on the exact literal patterns of `Six/ScheduleEncoding`. |
| [Six/TransitionClauses.lean](SmpMax/Six/TransitionClauses.lean) | Clause family 4, the transition clauses, holds for a legal schedule: `stopTrans_sat`, `shapeClauses_sat`, `noRevisit_sat` (from `noRevisit_sem`, plan L5.9), `visUpdate_sat`, assembled as `transition_sat`. |
| [Six/SelectionClauses.lean](SmpMax/Six/SelectionClauses.lean) | Clause families 10–12 hold: `selector_sat`, `ladder_sat` (strictly increasing selections), `block_sat6` (a selected matching admits no blocking pair, via `PM_sem` / `PW_sem`); the index list `idxsOf` of a read-off's stable matchings and `stableCount6_eq_filter_permsN`. |
| [Six/CubeUnits.lean](SmpMax/Six/CubeUnits.lean) | The cube's unit clauses hold under the witness assignment: `prefixUnits_sat`, `stopUnits_sat`; `cubeFormula_sat_of` packages base formula plus units. |
| [Six/LowerBound.lean](SmpMax/Six/LowerBound.lean) | The dihedral Latin instance `dihedral6` (OEIS A351413) and `dihedral6_count : stableCount6 dihedral6 = 48` by kernel `decide` over the 720 permutations; `f6_lower`. |
| [Six/CampaignSplits.lean](SmpMax/Six/CampaignSplits.lean) | Data generated from the journal: the ids of the depth-2 and depth-3 cubes the campaign split (`isSplitDepth2`, `isSplitDepth3`) and `finalCubes := refineCubes (refineCubes canonicalCubes2 isSplitDepth2) isSplitDepth3`, the certified cube set (numbers: `docs/results.md`). |
| [Six/CubeCoverage.lean](SmpMax/Six/CubeCoverage.lean) | Every legal first-appearance canonical schedule fits a well-formed cube of `finalCubes` (`fits_final`), from `cube_of_canonical` (a root cube fits), `fits_refine` (fitting survives a split round, for any split predicate) and the `*_WF` lemmas (plan L3.17–L3.20). |
| [Six/EncodingFaithfulness.lean](SmpMax/Six/EncodingFaithfulness.lean) | `schedCNF_sat` (the twelve family lemmas assembled), `cube_faithful6` (a legal schedule of at most 15 steps whose read-off has at least 49 stable matchings makes every fitting well-formed cube satisfiable at target 49), `exists_canonical_schedule` (from `49 ≤ stableCount6 I` to such a schedule, via `validity_unconditional`, `sigmaOf` and the count chain) and `f6_upper_of_unsat_of_coverage`. |
| [Six/ExactMaximum.lean](SmpMax/Six/ExactMaximum.lean) | `f6_upper_of_unsat` (coverage discharged by `fits_final`) and `f6_eq_48_of_unsat` (adds `f6_lower`). |

### The 1 + 25 theorems CI checks

`.github/workflows/lean-verify.yml` prints the axioms of
`f5_eq_16_of_unsat` and of 25 order-6 theorems and requires
`[propext, Classical.choice, Quot.sound]` for each; `docs/verification.md`
explains the trust boundary; the module map above describes each theorem. By file:
`bridge` (Six/ReadOff); `chain_complete`, `traj_mem_iff`, `wtraj_nodup`,
`total_moves_le_30` (Six/Chains, on the toolkit of Six/Lattice); `count_le_of_orderPreserving`
(Six/OrderPreservingBridge); `sc_le_readoffS_chainSched` (Six/ScheduleDominance);
`manOpt_wrelabel6`, `validity_unconditional` (Six/NormalizeMatching); `PM_sem`,
`PW_sem` (Six/ReadOffSemantics); `Legal_length_le_15` (Six/ScheduleLength);
`minFirst_mem_cyclicShapes`, `permsN6_perm_permutations`,
`Legal_map_minFirst` (Six/CyclicShapes); `SchedCNF6.dec_pwVar3` (Six/VariableDecoding);
`firstApp_relabel` (Six/FirstAppearance); `Legal_relabel`,
`sc_le_readoffS_relabelSched` (Six/ScheduleRelabeling);
`exists_canonical_schedule`, `cube_faithful6` (Six/EncodingFaithfulness);
`fits_final` (Six/CubeCoverage); `dihedral6_count` (Six/LowerBound);
`f6_upper_of_unsat`, `f6_eq_48_of_unsat` (Six/ExactMaximum). CI also checks that
`checks/FiveWitness.lean` depends on `[propext]` alone.

## Exporters

Three executables, declared in `lakefile.toml`, print DIMACS and cube
ids from the definitions above. They are the only bridge between the
theorem statements and the files the solvers and cake_lpr saw; the
printed output is what the identity checks compare against.

| executable | source | command |
|---|---|---|
| `export_cnf` | `ExportFiveCnf.lean` (order 5) | `lake build export_cnf`, then run `.lake/build/bin/export_cnf` in an empty directory: writes `perms120.txt`, the 120 production cubes `cubeL000.cnf` … `cubeL119.cnf` (`cubeCNF row`, 17 slots) and the 120 positive controls `cubeL16_000.cnf` … `cubeL16_119.cnf` (`cubeCNF16 row`, 16 slots). |
| `export_sched_cnf` | `ExportSixCnf.lean` (order 6) | `export_sched_cnf OUT [--n=N] [--k=K] [--prefix=a,b;c,d,e] [--stop]`: the base formula `schedCNFn N K` (defaults N = 6, K = 49, i.e. `schedCNF49`), or the cube formula for a prefix in the driver's id syntax; `--stop` closes the cube. Examples: open cube `0,1;2,3` is `--prefix='0,1;2,3'`; closed cube `0,1;stop` is `--prefix='0,1' --stop`; the root cube `stop` is `--stop` alone. Quote the argument (the ids contain semicolons). |
| `export_cubes6` | `ExportSixCubes.lean` (order 6) | `export_cubes6 OUT` prints the ids of `canonicalCubes2` (the root cubes); `--parents=FILE` prints `parent<TAB>child` for every `extendCanon` child of each id in FILE; `--final` prints the ids of `finalCubes` (the certified leaves); `--units=FILE` prints each id's unit clauses (`prefixUnits` then `stopUnits`, DIMACS lines joined by `\|`), the input of `tools/campaign/verify_lean_hashes.py`. |

Build all three with `lake build export_cnf export_sched_cnf export_cubes6`;
binaries land in `.lake/build/bin/`. The full identity-check recipe
(what to compare with the journal, expected line counts and hashes) is in
`docs/verification.md`; the recorded run is `results/f6/campaign-2026-09-08/lean_identity.txt`.

## Build, axiom and kernel-replay commands

From this directory (`lean`):

```bash
lake exe cache get          # prebuilt Mathlib
lake build                  # kernel-checks every theorem
! grep -rn sorry SmpMax/     # must print nothing

printf 'import SmpMax.Five.ExactMaximum\n#print axioms f5_eq_16_of_unsat\n' > /tmp/ax5.lean
lake env lean /tmp/ax5.lean
# 'f5_eq_16_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]

printf 'import SmpMax.Six.ExactMaximum\n#print axioms f6_eq_48_of_unsat\n#check @f6_eq_48_of_unsat\n' > /tmp/ax6.lean
lake env lean /tmp/ax6.lean
# 'f6_eq_48_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
# followed by the statement shown above

lake env lean checks/FiveWitness.lean
# 'witness_has_16_stable_matchings' depends on axioms: [propext]
```

The full axiom list is in [check_lean.sh](../tools/check_lean.sh), called by
CI. Run `bash tools/check_lean.sh` from the repository root to reproduce it.

Kernel replay with Lean's built-in `leanchecker` (every declaration of
every module re-checked by the kernel; silent exit 0 per module, about
8 s each; the recorded run of 2026-09-09 is
`results/f6/campaign-2026-09-08/leanchecker_2026-09-09.txt`, 38 / 38 clean before this path migration):

```bash
for m in $(grep -oE '^import SmpMax\.[[:alnum:]_.]+' SmpMax.lean | sed 's/import //') SmpMax; do
  lake env leanchecker "$m" || exit 1
done
```

## Separate checks

`SmpMax/Checks/FourLratPilot.lean` and `SmpMax/Checks/FiveCountCrossCheck.lean`
are not imported by the library. `tools/check_lean.sh` runs both separately:
the order-4 LRAT pilot and 300 differential order-5 count cases.
`tools/generate_five_witness.py` generates `lean/checks/FiveWitness.lean`.
