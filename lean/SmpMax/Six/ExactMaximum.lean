import SmpMax.Six.CubeCoverage
import SmpMax.Six.EncodingFaithfulness
import SmpMax.Six.LowerBound

/-!
# f(6) = 48: the assembled theorem (plan §7, L7.2–L7.4)

`f6_upper_of_unsat`: if every cube of `Cubes6.finalCubes` — the cube set
the campaign certified (`SplitList6.lean`: the 25,493 root cubes refined by
the 1,804 + 952 recorded splits; 318,736 leaves, printed by
`export_cubes6 --final` and equal to the journal's `verified` ids) — has an
unsatisfiable formula `cubeFormula 49 c`, then no well-formed order-6
instance has more than 48 stable matchings.  The hypothesis is discharged
outside the kernel by the campaign's cake_lpr-checked certificates
(`docs/reference/campaign.md`), exactly as `f5_upper_of_unsat`'s is by the 120 order-5
certificates.

Chain: `exists_canonical_schedule` (Faithfulness6: instance with ≥ 49 →
legal first-appearance-canonical schedule with read-off count ≥ 49) →
`fits_final` (Coverage6: such a schedule fits a cube of `finalCubes`) →
`cube_faithful6` (Faithfulness6: the witness assignment satisfies that
cube's formula).  `f6_eq_48_of_unsat` adds the kernel-checked dihedral
witness `f6_lower` (Lower6).
-/

open Cubes6

/-- **f(6) ≤ 48**, conditional on the campaign's certificates. -/
theorem f6_upper_of_unsat
    (H : ∀ c ∈ finalCubes, ¬ Satisfiable (cubeFormula 49 c)) :
    ∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48 :=
  f6_upper_of_unsat_of_coverage (fun _ hL hcan => fits_final hL hcan) H

/-- **f(6) = 48**, conditional on the campaign's certificates: the upper
bound for every well-formed order-6 instance and a witness with exactly 48
stable matchings, in one statement over one `stableCount6`. -/
theorem f6_eq_48_of_unsat
    (H : ∀ c ∈ finalCubes, ¬ Satisfiable (cubeFormula 49 c)) :
    (∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48) ∧
    (∃ I : Inst6, WF6 I = true ∧ stableCount6 I = 48) :=
  ⟨f6_upper_of_unsat H, f6_lower⟩
