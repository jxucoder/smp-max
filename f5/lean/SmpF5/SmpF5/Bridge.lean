import SmpF5.Symmetry
import SmpF5.Encoding
import SmpF5.Faithfulness

/-!
# Assembly: from 120 UNSAT cubes to f(5) ≤ 16

`cube_faithful` (the remaining proof obligation) extracts a satisfying
assignment of `cubeCNF row` from any well-formed instance in that cube
with ≥ 17 stable matchings. Everything else is proved:
`f5_upper_of_unsat` combines it with the symmetry reduction
(`reduce_man0'`) and the covering lemma (`cube_covering`).

The 120 hypotheses `¬ Satisfiable (cubeCNF row)` are discharged outside
the kernel: the formulas are printed verbatim from these definitions by
`export_cnf`, refuted by kissat, and the proofs checked end-to-end by the
formally verified checker cake_lpr (see `f5/cubesL/`).
-/

/-- **Faithfulness** (proved in `Faithfulness.lean`): a well-formed
instance with man 0 ranking identically, man 1's rank row equal to `row`,
and at least 17 stable matchings yields a satisfying assignment of
`cubeCNF row`. -/
theorem cube_faithful {I : Inst} (h : WF I = true)
    (h0 : I.mrank.getD 0 [] = idRow) {row : List Nat}
    (h1 : I.mrank.getD 1 [] = row)
    (hcnt : 17 ≤ stableCount I) :
    Satisfiable (cubeCNF row) :=
  cube_faithful' h h0 h1 hcnt

/-- **Main conditional theorem**: if all 120 cube formulas are
unsatisfiable, then no well-formed 5×5 instance has more than 16 stable
matchings. -/
theorem f5_upper_of_unsat
    (H : ∀ row ∈ perms120, ¬ Satisfiable (cubeCNF row)) :
    ∀ I : Inst, WF I = true → stableCount I ≤ 16 := by
  apply reduce_man0'
  intro I hWF h0
  by_contra hgt
  push_neg at hgt
  have hrow : I.mrank.getD 1 [] ∈ perms120 := cube_covering I hWF
  exact H _ hrow (cube_faithful hWF h0 rfl (by omega))
