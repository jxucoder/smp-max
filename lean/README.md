# Lean development

One Lake project contains both orders. `SmpMax/Five/` and `SmpMax/Six/`
are module groups; mathematical declaration names are preserved from the
original `SmpF5` project. The order-6 files reuse some helpers from order 5.

From the repository root:

```bash
(cd lean && lake exe cache get)
bash tools/check_lean.sh
```

Lean and Mathlib are pinned to v4.33.1; exact dependencies are in
[lake-manifest.json](lake-manifest.json). [Verification](../docs/verification.md)
explains the trust boundary and external certificate checks.

## Order-5 reading order

| Module | Content / main statement |
|---|---|
| [Definitions](SmpMax/Five/Definitions.lean) | `Inst`, `WF`, `isStable`, `stableCount`, and cube coverage |
| [Symmetry](SmpMax/Five/Symmetry.lean) | Normalize man 0's ranking by relabeling women |
| [Encoding](SmpMax/Five/Encoding.lean) | Lean-defined selector CNFs |
| [EncodingFaithfulness](SmpMax/Five/EncodingFaithfulness.lean) | A counterexample gives a satisfying cube assignment |
| [UpperBound](SmpMax/Five/UpperBound.lean) | `f5_upper_of_unsat` |
| [ExactMaximum](SmpMax/Five/ExactMaximum.lean) | `witnessI`, `witness_count`, `f5_eq_16_of_unsat` |

## Order-6 reading order

| Layer | Modules | Role |
|---|---|---|
| Instances and read-off | [ReadOff](SmpMax/Six/ReadOff.lean), [OrderPreservingBridge](SmpMax/Six/OrderPreservingBridge.lean) | Definitions, `bridge`, and abstract count preservation |
| Stable-matching structure | [Lattice](SmpMax/Six/Lattice.lean), [Chains](SmpMax/Six/Chains.lean), [CycleDecomposition](SmpMax/Six/CycleDecomposition.lean) | Maximal chains, trajectories, and cyclic steps |
| Schedule reduction | [Schedule](SmpMax/Six/Schedule.lean), [ChainToSchedule](SmpMax/Six/ChainToSchedule.lean), [ScheduleDominance](SmpMax/Six/ScheduleDominance.lean), [NormalizeMatching](SmpMax/Six/NormalizeMatching.lean) | Legality and `validity_unconditional` |
| Relabeling | [Relabeling](SmpMax/Six/Relabeling.lean) | Instance-level label invariance |
| Exact formula and cube definitions | [ScheduleEncoding](SmpMax/Six/ScheduleEncoding.lean), [CampaignCubes](SmpMax/Six/CampaignCubes.lean) | Campaign-compatible clause and cube lists |
| Assignment construction | [VariableDecoding](SmpMax/Six/VariableDecoding.lean), [TrajectoryPrefixes](SmpMax/Six/TrajectoryPrefixes.lean), [CyclicShapes](SmpMax/Six/CyclicShapes.lean), [FrameAssignment](SmpMax/Six/FrameAssignment.lean) | Variable layout and schedule semantics |
| Semantic bounds | [ReadOffSemantics](SmpMax/Six/ReadOffSemantics.lean), [ScheduleLength](SmpMax/Six/ScheduleLength.lean) | `PM_sem`, `PW_sem`, and `Legal_length_le_15` |

The [remaining faithfulness/coverage plan](../docs/design/f6-faithfulness.md)
is still active. The default library build does not constitute a completed
order-6 upper-bound theorem.

## Exporters and separate checks

| Source / target | Purpose |
|---|---|
| [ExportFiveCnf.lean](ExportFiveCnf.lean), `lake build export_cnf` | All 120 upper-bound cubes and 120 threshold-16 positive controls |
| [ExportSixCnf.lean](ExportSixCnf.lean), `lake build export_sched_cnf` | Schedule base or prefix cube in DIMACS |
| [ExportSixCubes.lean](ExportSixCubes.lean), `lake build export_cubes6` | Canonical roots or split-child lists |
| [FiveWitness.lean](checks/FiveWitness.lean) | Standalone import-free count proof, axiom `propext` only |
| [FiveCountCrossCheck.lean](SmpMax/Checks/FiveCountCrossCheck.lean) | 300 differential count cases |
| [FourLratPilot.lean](SmpMax/Checks/FourLratPilot.lean) | Embedded order-4 LRAT proof pilot |

The established executable names remain stable. All paths in the table
are relative to `lean/`; the check script runs the separate checks explicitly.
Proof statements, proof bodies, and formula definitions were preserved
during renaming; see [layout validation](../docs/layout-verification.md).
