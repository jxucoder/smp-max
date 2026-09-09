import SmpF5.ReadoffSem6
import SmpF5.SchedLen6

/-!
# Clause families 10–12: selector, ladder, block (plan §6 items 10–12)

Satisfaction, under the assignment `tau6 k S idxs` of `Frames6`, of the
three selector-block clause families of `SchedCNF6`:

* `selector_sat` — `selectorClauses (layout 6) k`: every slot picks an
  index (`[Y t 0 .. Y t 719]`), `Y ⇒ Pf`, and the ladder-internal
  clauses tying `Pf t i` to `Pf t (i-1)` and `Y t i`;
* `ladder_sat` — `ladderClauses (layout 6) k`: consecutive slots select
  strictly increasing indices (`idxs.Pairwise (· < ·)`);
* `block_sat6` — `blockClauses (layout 6) k (permsN 6)`: a selected
  matching admits no blocking pair.  The men's/women's preference
  variables are turned into read-off rank comparisons by `PM_sem` /
  `PW_sem` (ReadoffSem6) and `get2_readoffS_mrank` / `get2_readoffS_wrank`
  (ValidityBridge6), and the `(m, w)` case of
  `isStable6 (readoffS S) mu` closes the clause.

Also L4.18 `stableCount6_eq_filter_permsN` (plan §4.3) and the index list
`idxsOf R` of plan §7 with its four properties (`idxsOf_length`,
`idxsOf_pairwise`, `idxsOf_lt`, `idxsOf_stable`).

No deviation from the plan statements.  All helper lemmas live in
`namespace FamSelect6`; the plan-named lemmas are at the root.
-/

open SchedCNF6

namespace FamSelect6

/-! ## Layout projections at order 6 -/

theorem layout6_NP : (layout 6).NP = 720 := by rw [layout6_eq]

theorem layout6_n : (layout 6).n = 6 := by rw [layout6_eq]

/-! ## Core `List.idxOf` is the repository's `idxOf` -/

theorem idxOf_eq (w : Nat) : ∀ (l : List Nat), l.idxOf w = idxOf w l
  | [] => by simp [idxOf]
  | y :: ys => by
    rw [List.idxOf_cons]
    by_cases h : y = w
    · simp [h, idxOf]
    · simp [h, idxOf, idxOf_eq w ys, Bool.cond_eq_ite]

theorem invOf_eq {mu : List Nat} {w : Nat} : invOf mu w = idxOf w mu := idxOf_eq w mu

/-! ## `permsN 6` entries -/

theorem permsN6_getD_perm {i : Nat} (hi : i < 720) : ((permsN 6).getD i []).Perm idRow6 := by
  have hlt : i < (permsN 6).length := by rw [permsN6_length]; exact hi
  rw [List.getD_eq_getElem _ _ hlt]
  exact mem_permsN6.1 (List.getElem_mem hlt)

/-! ## Positivity of the variable ids that occur in families 10–12 -/

theorem yVar_pos (t i : Nat) : 0 < yVar (layout 6) t i := by rw [yVar6]; omega

theorem pfVar_pos (k t i : Nat) : 0 < pfVar (layout 6) k t i := by rw [pfVar6]; omega

theorem pmVar_pos (m a b : Nat) : 0 < pmVar (layout 6) m a b := by rw [pmVar6]; omega

theorem pwVar_pos (w a b i : Nat) : 0 < pwVar (layout 6) w a b i := by rw [pwVar6]; omega

/-! ## The assignment on the variables of families 10–12 -/

section
variable {k : Nat} {S : List (List Nat)} {idxs : List Nat}

theorem tau6_yVar {t i : Nat} (ht : t < k) (hi : i < 720) :
    tau6 k S idxs (yVar (layout 6) t i) = decide (idxs.getD t 720 = i) := by
  unfold tau6; rw [dec_yVar ht hi]; rfl

theorem tau6_pfVar {t i : Nat} (ht : t < k) (hi : i < 720) :
    tau6 k S idxs (pfVar (layout 6) k t i) = decide (idxs.getD t 720 ≤ i) := by
  unfold tau6; rw [dec_pfVar ht hi]; rfl

theorem tau6_pmVar {m a b : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (pmVar (layout 6) m a b) = τV S idxs (.PM m a b) := by
  unfold tau6; rw [dec_pmVar hm hab ha hb]

theorem tau6_pwVar0 {w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (pwVar (layout 6) w a b 0) = τV S idxs (.PW w a b) := by
  unfold tau6; rw [dec_pwVar0 hw hab ha hb]

theorem eval_pos_yVar {t i : Nat} (ht : t < k) (hi : i < 720) :
    evalLit (tau6 k S idxs) (pos (yVar (layout 6) t i)) = decide (idxs.getD t 720 = i) := by
  rw [evalLit_pos6 _ (yVar_pos t i), tau6_yVar ht hi]

theorem eval_neg_yVar {t i : Nat} (ht : t < k) (hi : i < 720) :
    evalLit (tau6 k S idxs) (neg (yVar (layout 6) t i)) = !decide (idxs.getD t 720 = i) := by
  rw [evalLit_neg6 _ (yVar_pos t i), tau6_yVar ht hi]

theorem eval_pos_pfVar {t i : Nat} (ht : t < k) (hi : i < 720) :
    evalLit (tau6 k S idxs) (pos (pfVar (layout 6) k t i)) = decide (idxs.getD t 720 ≤ i) := by
  rw [evalLit_pos6 _ (pfVar_pos k t i), tau6_pfVar ht hi]

theorem eval_neg_pfVar {t i : Nat} (ht : t < k) (hi : i < 720) :
    evalLit (tau6 k S idxs) (neg (pfVar (layout 6) k t i)) = !decide (idxs.getD t 720 ≤ i) := by
  rw [evalLit_neg6 _ (pfVar_pos k t i), tau6_pfVar ht hi]

theorem eval_neg_pmVar {m a b : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    evalLit (tau6 k S idxs) (neg (pmVar (layout 6) m a b)) = !τV S idxs (.PM m a b) := by
  rw [evalLit_neg6 _ (pmVar_pos m a b), tau6_pmVar hm hab ha hb]

theorem eval_neg_pwVar0 {w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    evalLit (tau6 k S idxs) (neg (pwVar (layout 6) w a b 0)) = !τV S idxs (.PW w a b) := by
  rw [evalLit_neg6 _ (pwVar_pos w a b 0), tau6_pwVar0 hw hab ha hb]

/-! ## The index list -/

theorem getD_mem_idxs {t : Nat} (ht : t < idxs.length) : idxs.getD t 720 ∈ idxs := by
  rw [List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

theorem getD_lt_succ {t : Nat} (hpair : idxs.Pairwise (· < ·)) (ht : t + 1 < idxs.length) :
    idxs.getD t 720 < idxs.getD (t + 1) 720 := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ ht]
  exact List.pairwise_iff_getElem.mp hpair t (t + 1) (by omega) ht (by omega)

end

/-! ## Filtering a range of indices (f(5) `Faithfulness.lean` pattern) -/

theorem map_getD_range_len {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem h2]

theorem filter_range_length {α : Type} (l : List α) (p : α → Bool) (d : α) :
    ((List.range l.length).filter (fun i => p (l.getD i d))).length
      = (l.filter p).length := by
  conv_rhs => rw [← map_getD_range_len l d]
  rw [List.filter_map, List.length_map]
  rfl

end FamSelect6

open FamSelect6

/-! ## Family 10: `selectorClauses` -/

theorem selector_sat {k : Nat} {S : List (List Nat)} {idxs : List Nat}
    (hk : k ≤ idxs.length) (hmem : ∀ i ∈ idxs, i < 720) :
    (selectorClauses (layout 6) k).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [selectorClauses, layout6_NP, List.mem_flatMap, List.mem_range, List.mem_cons] at hc
  obtain ⟨t, ht, hc⟩ := hc
  have htl : t < idxs.length := by omega
  have hsel : idxs.getD t 720 < 720 := hmem _ (getD_mem_idxs htl)
  rcases hc with hc | ⟨i, hi, hc⟩
  · -- the slot is nonempty: the literal `Y t (idxs[t])` is true
    -- (`rw` rather than a `rfl` pattern: unifying against the closed
    -- `List.range 720` would unfold it)
    rw [hc, evalClause, List.any_eq_true]
    refine ⟨pos (yVar (layout 6) t (idxs.getD t 720)),
      List.mem_map.2 ⟨_, List.mem_range.2 hsel, rfl⟩, ?_⟩
    rw [eval_pos_yVar ht hsel]
    exact decide_eq_true rfl
  · rcases hc with rfl | hc
    · -- `[-Y t i, Pf t i]`
      simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        eval_neg_yVar ht hi, eval_pos_pfVar ht hi, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, decide_eq_true_eq]
      omega
    · by_cases hi0 : i > 0
      · rw [if_pos hi0] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        have hi1 : i - 1 < 720 := by omega
        rcases hc with rfl | rfl
        · -- `[-Pf t (i-1), Pf t i]`
          simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
            eval_neg_pfVar ht hi1, eval_pos_pfVar ht hi, Bool.or_eq_true, Bool.not_eq_true',
            decide_eq_false_iff_not, decide_eq_true_eq]
          omega
        · -- `[-Pf t i, Pf t (i-1), Y t i]`
          simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
            eval_neg_pfVar ht hi, eval_pos_pfVar ht hi1, eval_pos_yVar ht hi, Bool.or_eq_true,
            Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
          omega
      · rw [if_neg hi0] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        -- `[-Pf t 0, Y t 0]`
        simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
          eval_neg_pfVar ht (by omega : 0 < 720), eval_pos_yVar ht (by omega : 0 < 720),
          Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
        omega

/-! ## Family 11: `ladderClauses` -/

theorem ladder_sat {k : Nat} {S : List (List Nat)} {idxs : List Nat}
    (hk : k ≤ idxs.length) (hpair : idxs.Pairwise (· < ·)) :
    (ladderClauses (layout 6) k).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [ladderClauses, layout6_NP, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.mem_map] at hc
  obtain ⟨t, ht, hc⟩ := hc
  have ht1 : t + 1 < k := by omega
  have htk : t < k := by omega
  have hmono := getD_lt_succ hpair (by omega : t + 1 < idxs.length)
  rcases hc with rfl | ⟨j', hj', rfl⟩
  · -- `[-Y (t+1) 0]`
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
      eval_neg_yVar ht1 (by omega : 0 < 720), Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  · -- `[-Y (t+1) (j'+1), Pf t j']`
    have hj : j' + 1 < 720 := by omega
    simp only [Nat.add_sub_cancel, evalClause, List.any_cons, List.any_nil, Bool.or_false,
      eval_neg_yVar ht1 hj, eval_pos_pfVar htk (by omega : j' < 720), Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega

/-! ## Family 12: `blockClauses` -/

theorem block_sat6 {k : Nat} {S : List (List Nat)} {idxs : List Nat}
    (hL : Legal S) (hlen : S.length ≤ 15) (hk : k ≤ idxs.length)
    (hstab : ∀ i ∈ idxs, i < 720 ∧ isStable6 (readoffS S) ((permsN 6).getD i []) = true) :
    (blockClauses (layout 6) k (permsN 6)).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [blockClauses, layout6_n, permsN6_length, List.mem_flatMap, List.mem_range,
    List.mem_filterMap] at hc
  obtain ⟨t, ht, i, hi, m, hm, w, hw, hite⟩ := hc
  set mu := (permsN 6).getD i [] with hmu
  by_cases hwm : w = mu.getD m 0
  · rw [if_pos hwm] at hite
    exact absurd hite (by simp)
  · rw [if_neg hwm] at hite
    obtain rfl := (Option.some.inj hite).symm
    rw [invOf_eq]
    have hp : mu.Perm idRow6 := permsN6_getD_perm hi
    have hwm6 : mu.getD m 0 < 6 := perm6_getD_lt hp hm
    have hinv6 : idxOf w mu < 6 := idxOf_lt6 hp hw
    have hmne : m ≠ idxOf w mu := by
      intro he
      apply hwm
      rw [he]
      exact (getD_idxOf (perm6_mem hp hw)).symm
    have e1 := eval_neg_yVar (S := S) (idxs := idxs) ht hi
    have e2 := eval_neg_pmVar (k := k) (S := S) (idxs := idxs) hm hwm hw hwm6
    have e3 := eval_neg_pwVar0 (k := k) (S := S) (idxs := idxs) hw hmne hm hinv6
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false, e1, e2, e3,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases hy : idxs.getD t 720 = i
    · -- slot `t` selects `mu`: it is stable in `readoffS S`, so one of the
      -- two preference variables is false
      right
      have htl : t < idxs.length := by omega
      have himem : i ∈ idxs := hy ▸ getD_mem_idxs htl
      obtain ⟨_, hst⟩ := hstab i himem
      have hPM := PM_sem (idxs := idxs) hL hlen hm hw hwm6
      have hPW := PW_sem (idxs := idxs) hL hlen hw hm hinv6
      rw [← get2_readoffS_mrank hm hw, ← get2_readoffS_mrank hm hwm6] at hPM
      rw [← get2_readoffS_wrank hw hm, ← get2_readoffS_wrank hw hinv6] at hPW
      simp only [isStable6, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_true_eq, decide_eq_false_iff_not] at hst
      rcases hst m hm w hw with heq | h1 | h2
      · exact absurd heq hwm
      · left
        rw [Bool.eq_false_iff]
        exact fun hc => h1 (hPM.1 hc)
      · right
        rw [Bool.eq_false_iff]
        exact fun hc => h2 (hPW.1 hc)
    · left
      exact hy

/-! ## L4.18: `stableCount6` over `permsN 6` -/

theorem stableCount6_eq_filter_permsN (R : Inst6) :
    stableCount6 R = ((permsN 6).filter (isStable6 R)).length := by
  unfold stableCount6 sms6
  exact (permsN6_perm_permutations.filter (isStable6 R)).length_eq.symm

/-! ## The index list of plan §7 -/

/-- The sorted list of indices `i < 720` such that `(permsN 6)[i]` is a
stable matching of `R`. -/
def idxsOf (R : Inst6) : List Nat :=
  (List.range 720).filter (fun i => isStable6 R ((permsN 6).getD i []))

theorem idxsOf_length (R : Inst6) : (idxsOf R).length = stableCount6 R := by
  have h := filter_range_length (permsN 6) (isStable6 R) []
  rw [permsN6_length] at h
  unfold idxsOf
  rw [stableCount6_eq_filter_permsN, ← h]

theorem idxsOf_pairwise (R : Inst6) : (idxsOf R).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem idxsOf_lt (R : Inst6) : ∀ i ∈ idxsOf R, i < 720 := by
  intro i hi
  exact List.mem_range.1 (List.mem_filter.1 hi).1

theorem idxsOf_stable (R : Inst6) :
    ∀ i ∈ idxsOf R, isStable6 R ((permsN 6).getD i []) = true := by
  intro i hi
  exact (List.mem_filter.1 hi).2
