import SmpF5.ReadoffSem6

/-!
# Clause families 1–3: initial state, matching one-hot, step one-hot (plan §6 items 1–3)

Implements `f6/FAITHFULNESS_PLAN.md` §6 items 1–3 for the order-6 schedule
CNF `SchedCNF6`: under the assignment `tau6 k S idxs` (any `k`, `idxs`),

* `init_sat` — `initClauses (layout 6)` holds (frame 0 is the identity
  matching and the visited mask at frame 0 is the diagonal);
* `matching_sat` — `matchingClauses (layout 6)` holds when every step of
  `S` is well formed (each frame is a permutation of `idRow6`: rows are
  one-hot, columns injective);
* `step_sat` — `stepClauses (layout 6)` holds (the step choice at frame
  `t` is the one-hot `stepIdx S t ≤ 409`; once stopped, stopped).

The statements are exactly those of the plan; no deviations.  The
helpers in `namespace FamState6` evaluate the literals `pos`/`neg` of
`mVar`/`vVar`/`sVar` under `tau6` through the decode lemmas of
`Decode6.lean` (`dec_mVar`, `dec_vVar`, `dec_sVar`).
-/

open SchedCNF6

namespace FamState6

/-! ## The layout fields at order 6 -/

theorem lay_n : (layout 6).n = 6 := by rw [layout6_eq]
theorem lay_F : (layout 6).F = 15 := by rw [layout6_eq]
theorem lay_NS : (layout 6).NS = 409 := by rw [layout6_eq]

theorem mVar_pos (t m w : Nat) : 0 < mVar (layout 6) t m w := by rw [mVar6]; omega
theorem vVar_pos (t m w : Nat) : 0 < vVar (layout 6) t m w := by rw [vVar6]; omega
theorem sVar_pos (t j : Nat) : 0 < sVar (layout 6) t j := by rw [sVar6]; omega

theorem idRow6_getD {m : Nat} (hm : m < 6) : idRow6.getD m 0 = m := by
  rw [idRow6_eq_range, List.getD_eq_getElem _ _ (by simpa using hm)]
  simp

/-! ## Literal evaluation under `tau6` -/

variable {k : Nat} {S : List (List Nat)} {idxs : List Nat}

theorem tau6_mVar {t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    tau6 k S idxs (mVar (layout 6) t m w) = decide ((frame S t).getD m 0 = w) := by
  unfold tau6; rw [dec_mVar ht hm hw]; rfl

theorem tau6_vVar {t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    tau6 k S idxs (vVar (layout 6) t m w) = vis S t m w := by
  unfold tau6; rw [dec_vVar ht hm hw]; rfl

theorem tau6_sVar {t j : Nat} (ht : t < 15) (hj : j ≤ 409) :
    tau6 k S idxs (sVar (layout 6) t j) = decide (j = stepIdx S t) := by
  unfold tau6; rw [dec_sVar ht hj]; rfl

theorem eval_mVar_pos {t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    evalLit (tau6 k S idxs) (pos (mVar (layout 6) t m w)) =
      decide ((frame S t).getD m 0 = w) := by
  rw [evalLit_pos6 _ (mVar_pos t m w), tau6_mVar ht hm hw]

theorem eval_mVar_neg {t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    evalLit (tau6 k S idxs) (neg (mVar (layout 6) t m w)) =
      !decide ((frame S t).getD m 0 = w) := by
  rw [evalLit_neg6 _ (mVar_pos t m w), tau6_mVar ht hm hw]

theorem eval_vVar_pos {t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    evalLit (tau6 k S idxs) (pos (vVar (layout 6) t m w)) = vis S t m w := by
  rw [evalLit_pos6 _ (vVar_pos t m w), tau6_vVar ht hm hw]

theorem eval_vVar_neg {t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    evalLit (tau6 k S idxs) (neg (vVar (layout 6) t m w)) = !vis S t m w := by
  rw [evalLit_neg6 _ (vVar_pos t m w), tau6_vVar ht hm hw]

theorem eval_sVar_pos {t j : Nat} (ht : t < 15) (hj : j ≤ 409) :
    evalLit (tau6 k S idxs) (pos (sVar (layout 6) t j)) = decide (j = stepIdx S t) := by
  rw [evalLit_pos6 _ (sVar_pos t j), tau6_sVar ht hj]

theorem eval_sVar_neg {t j : Nat} (ht : t < 15) (hj : j ≤ 409) :
    evalLit (tau6 k S idxs) (neg (sVar (layout 6) t j)) = !decide (j = stepIdx S t) := by
  rw [evalLit_neg6 _ (sVar_pos t j), tau6_sVar ht hj]

end FamState6

open FamState6

/-! ## Family 1: `initClauses` -/

theorem init_sat (k : Nat) (S : List (List Nat)) (idxs : List Nat) :
    (initClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [initClauses, lay_n, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨m, hm, w, hw, hc⟩ := hc
  rcases hc with rfl | rfl
  · -- `M[0][m][w]` iff `m = w`
    by_cases hmw : m = w
    · rw [if_pos hmw]
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        eval_mVar_pos (t := 0) (by omega) hm hw, frame_zero, idRow6_getD hm]
      exact decide_eq_true hmw
    · rw [if_neg hmw]
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        eval_mVar_neg (t := 0) (by omega) hm hw, frame_zero, idRow6_getD hm,
        decide_eq_false hmw, Bool.not_false]
  · -- `V[0][m][w]` iff `m = w`
    by_cases hmw : m = w
    · rw [if_pos hmw]
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        eval_vVar_pos (t := 0) (by omega) hm hw, vis_zero hm]
      exact decide_eq_true hmw.symm
    · rw [if_neg hmw]
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        eval_vVar_neg (t := 0) (by omega) hm hw, vis_zero hm,
        decide_eq_false (Ne.symm hmw), Bool.not_false]

/-! ## Family 2: `matchingClauses` -/

theorem matching_sat {k : Nat} {S : List (List Nat)} {idxs : List Nat}
    (hWF : ∀ st ∈ S, WFStep st) :
    (matchingClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [matchingClauses, lay_n, lay_F, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.mem_append, List.mem_filterMap] at hc
  obtain ⟨t, ht, hc⟩ := hc
  have ht' : t ≤ 15 := by omega
  have hperm : (frame S t).Perm idRow6 := frame_perm hWF t
  rcases hc with ⟨m, hm, hc⟩ | ⟨w, hw, m1, hm1, m2, hm2, hite⟩
  · rcases hc with rfl | ⟨w1, hw1, w2, hw2, hite⟩
    · -- row `m` has a partner
      rw [evalClause, List.any_eq_true]
      have hlt : (frame S t).getD m 0 < 6 := perm6_getD_lt hperm hm
      refine ⟨pos (mVar (layout 6) t m ((frame S t).getD m 0)),
        List.mem_map.2 ⟨_, List.mem_range.2 hlt, rfl⟩, ?_⟩
      rw [eval_mVar_pos ht' hm hlt]
      exact decide_eq_true rfl
    · -- at most one partner in row `m`
      by_cases h12 : w1 < w2
      · rw [if_pos h12] at hite
        obtain rfl := Option.some.inj hite
        simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
          eval_mVar_neg ht' hm hw1, eval_mVar_neg ht' hm hw2, Bool.not_eq_true',
          decide_eq_false_iff_not]
        omega
      · rw [if_neg h12] at hite
        exact absurd hite (by simp)
  · -- at most one man in column `w`
    by_cases h12 : m1 < m2
    · rw [if_pos h12] at hite
      obtain rfl := Option.some.inj hite
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        eval_mVar_neg ht' hm1 hw, eval_mVar_neg ht' hm2 hw, Bool.not_eq_true',
        decide_eq_false_iff_not]
      by_cases h1 : (frame S t).getD m1 0 = w
      · right
        intro h2
        have := perm6_getD_inj hperm hm1 hm2 (h1.trans h2.symm)
        omega
      · left; exact h1
    · rw [if_neg h12] at hite
      exact absurd hite (by simp)

/-! ## Family 3: `stepClauses` -/

set_option linter.unusedVariables false in
theorem step_sat {k : Nat} {S : List (List Nat)} {idxs : List Nat}
    (hWF : ∀ st ∈ S, WFStep st) (hlen : S.length ≤ 15) :
    (stepClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [stepClauses, lay_F, lay_NS, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.mem_append, List.mem_filterMap] at hc
  obtain ⟨t, ht, hc⟩ := hc
  rcases hc with (rfl | ⟨a, ha, b, hb, hite⟩) | hc
  · -- some step is chosen: `j = stepIdx S t`
    rw [evalClause, List.any_eq_true]
    have hle : stepIdx S t ≤ 409 := stepIdx_le hWF t
    refine ⟨pos (sVar (layout 6) t (stepIdx S t)),
      List.mem_map.2 ⟨_, List.mem_range.2 (by omega), rfl⟩, ?_⟩
    rw [eval_sVar_pos ht hle]
    exact decide_eq_true rfl
  · -- at most one step is chosen
    by_cases hab : a < b
    · rw [if_pos hab] at hite
      obtain rfl := Option.some.inj hite
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        eval_sVar_neg ht (by omega : a ≤ 409), eval_sVar_neg ht (by omega : b ≤ 409),
        Bool.not_eq_true', decide_eq_false_iff_not]
      omega
    · rw [if_neg hab] at hite
      exact absurd hite (by simp)
  · -- stop absorbs: `S[t][0] → S[t+1][0]`
    by_cases ht1 : t + 1 < 15
    · rw [if_pos ht1] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
        eval_sVar_neg ht (by omega : 0 ≤ 409), eval_sVar_pos ht1 (by omega : 0 ≤ 409),
        Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      by_cases h0 : 0 = stepIdx S t
      · right
        have h1 : ¬ t < S.length := by rw [← stepIdx_pos_iff]; omega
        have h2 : ¬ 0 < stepIdx S (t + 1) := by rw [stepIdx_pos_iff]; omega
        omega
      · left; exact h0
    · rw [if_neg ht1] at hc
      exact absurd hc (List.not_mem_nil)
