import SmpMax.Five.UpperBound

/-!
# The lower bound and the combined statement

`stableCount` enumerates via `List.permutations`, which Lean's kernel
cannot reduce (well-founded recursion), so the witness count is
established via the structurally-recursive `List.permutations'` and
transported across `List.permutations_perm_permutations'`.
-/

/-- The 16-stable-matching witness found by SAT (see `papers/f5/f5-max-stable-matchings.tex`),
as rank tables. -/
def witnessI : Inst :=
  ⟨[[2, 0, 1, 4, 3], [1, 3, 4, 2, 0], [2, 4, 3, 0, 1], [4, 1, 0, 2, 3], [0, 2, 3, 4, 1]],
   [[1, 3, 2, 0, 4], [4, 1, 0, 3, 2], [2, 0, 1, 4, 3], [1, 2, 3, 4, 0], [0, 4, 3, 1, 2]]⟩

/-- Kernel-computable variant of `stableCount`. -/
def stableCount' (I : Inst) : Nat :=
  (([0, 1, 2, 3, 4] : List Nat).permutations'.filter (isStable I)).length

theorem stableCount_eq_stableCount' (I : Inst) :
    stableCount I = stableCount' I := by
  unfold stableCount stableCount'
  exact ((List.permutations_perm_permutations' _).filter _).length_eq

theorem witness_WF : WF witnessI = true := by decide

theorem witness_count : stableCount witnessI = 16 := by
  rw [stableCount_eq_stableCount']
  decide

/-- **f(5) = 16**, conditional on the 120 cube refutations (which are
checked outside the kernel by the formally verified checker cake_lpr;
see `results/f5/lean-cubes/` and `docs/verification.md`). -/
theorem f5_eq_16_of_unsat
    (H : ∀ row ∈ perms120, ¬ Satisfiable (cubeCNF row)) :
    (∀ I : Inst, WF I = true → stableCount I ≤ 16) ∧
    (∃ I : Inst, WF I = true ∧ stableCount I = 16) :=
  ⟨f5_upper_of_unsat H, witnessI, witness_WF, witness_count⟩
