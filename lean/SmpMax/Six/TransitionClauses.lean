import SmpMax.Six.ReadOffSemantics
import SmpMax.Six.ScheduleLength

/-!
# Clause family 4: the transition clauses (plan §5.2 L5.9, §6 item 4)

Implements `docs/design/f6-faithfulness.md` §5.2 (**L5.9** `noRevisit_sem`) and
§6 item 4 (`stopTrans_sat`, `shapeClauses_sat`, `noRevisit_sat`,
`visUpdate_sat`, `transition_sat`): under the assignment `tau6 k S idxs`
of a legal schedule `S`, every clause of
`SchedCNF6.transitionClauses (layout 6) (cyclicShapes 6)` is satisfied.

* Stop-copy clauses `[-S[t][0], -M[t][m][w], M[t+1][m][w]]`: `S[t][0]`
  true means `stepIdx S t = 0`, i.e. `S.length ≤ t` (`stepIdx_pos_iff`),
  and `frame_succ_stop` copies the frame.
* Shape clauses (`SchedCNF6.shapeClauses L t (j'+1) SH[j']`): `S[t][j'+1]`
  true means `j'+1 = stepIdx S t`, so `t < S.length` and `SH[j'] =
  minFirst (S.getD t [])` (`shape_of_stepIdx`); then `frame S (t+1) =
  applyStep SH[j'] (frame S t)` (`frame_succ_step`, `applyStep_minFirst`)
  and `applyStep_getD` gives both clause shapes: man `sh[i]` takes the
  wife of `sh[(i+1) % kk]` (`idxOf_getD` on the duplicate-free shape), a
  man outside the shape keeps his wife.
* No-revisit `[-M[t+1][m][w], M[t][m][w], -V[t][m][w]]`: for `t <
  S.length` this is `noRevisit_sem` — a man's destuttered partner column
  (`strajM S m`) is duplicate-free, so a partner regained after a change
  would be a repeat (`destutter_noReturn`); for `S.length ≤ t` the two
  frames coincide.
* Visited update (three clauses): `vis_succ`.

The decomposition follows `transitionClauses` literally, one lemma per
appended block, at a fixed frame `t < 15`; `L.n`, `L.F` are written as
`6`, `15` (`(layout 6).n = 6` and `(layout 6).F = 15` hold by `rfl`).
Signatures: `stopTrans_sat (ht : t < 15)`,
`shapeClauses_sat (hL : Legal S) (ht : t < 15) (hj : j' < 409)`,
`noRevisit_sat (hL : Legal S) (ht : t < 15)`, `visUpdate_sat (ht : t < 15)`,
`transition_sat (hL : Legal S) (hlen : S.length ≤ 15)` (`hlen` is not
needed by the proof — every frame bound comes from the loop bounds — but
is kept as in the plan).  No deviations from the plan statements.
-/

open SchedCNF6

namespace FamTrans6

/-! ## Layout projections and literal evaluation -/

theorem layout6_n : (layout 6).n = 6 := rfl
theorem layout6_F : (layout 6).F = 15 := rfl

theorem mVar_pos (L : Lay) (t m w : Nat) : 0 < mVar L t m w := by unfold mVar; omega
theorem vVar_pos (L : Lay) (t m w : Nat) : 0 < vVar L t m w := by unfold vVar; omega
theorem sVar_pos (L : Lay) (t j : Nat) : 0 < sVar L t j := by unfold sVar sBase; omega

theorem tau_M {k : Nat} (S : List (List Nat)) (idxs : List Nat) (t m w : Nat)
    (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    tau6 k S idxs (mVar (layout 6) t m w) = decide ((frame S t).getD m 0 = w) := by
  unfold tau6; rw [dec_mVar ht hm hw]; rfl

theorem tau_V {k : Nat} (S : List (List Nat)) (idxs : List Nat) (t m w : Nat)
    (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    tau6 k S idxs (vVar (layout 6) t m w) = vis S t m w := by
  unfold tau6; rw [dec_vVar ht hm hw]; rfl

theorem tau_S {k : Nat} (S : List (List Nat)) (idxs : List Nat) (t j : Nat)
    (ht : t < 15) (hj : j ≤ 409) :
    tau6 k S idxs (sVar (layout 6) t j) = decide (j = stepIdx S t) := by
  unfold tau6; rw [dec_sVar ht hj]; rfl

theorem evalClause2 (τ : Nat → Bool) (l₁ l₂ : Int) :
    evalClause τ [l₁, l₂] = (evalLit τ l₁ || evalLit τ l₂) := by
  simp [evalClause]

theorem evalClause3 (τ : Nat → Bool) (l₁ l₂ l₃ : Int) :
    evalClause τ [l₁, l₂, l₃] = (evalLit τ l₁ || evalLit τ l₂ || evalLit τ l₃) := by
  simp [evalClause, Bool.or_assoc]

/-! ## A duplicate-free destutter never returns to a value it has left -/

/-- In `a :: l`, if the destuttered list is duplicate-free, a value that
occurred among the first `k+1` entries and differs from entry `k` cannot
be entry `k+1`. -/
theorem destutter'_noReturn : ∀ (l : List Nat) (a : Nat),
    (l.destutter' (· ≠ ·) a).Nodup →
    ∀ (k w : Nat), k + 1 < (a :: l).length → w ∈ (a :: l).take (k + 1) →
      (a :: l).getD k 0 ≠ w → (a :: l).getD (k + 1) 0 ≠ w := by
  intro l
  induction l with
  | nil =>
    intro a _ k w hk _ _
    simp at hk
  | cons b l ih =>
    intro a hnd k w hk hw hne
    by_cases hab : a ≠ b
    · rw [List.destutter'_cons_pos (l := l) hab] at hnd
      have hnd' := List.nodup_cons.1 hnd
      cases k with
      | zero =>
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hw
        simp only [List.getD_cons_zero] at hne
        exact absurd hw.symm hne
      | succ k =>
        rw [List.take_succ_cons, List.mem_cons] at hw
        simp only [List.length_cons] at hk
        rw [List.getD_cons_succ] at hne ⊢
        rcases hw with rfl | hw
        · -- `w = a`: `a` never reappears after leaving (`a ∉ destutter' b l`)
          have hnot : w ∉ b :: l := by
            intro h
            apply hnd'.1
            rw [mem_destutter'_ne_iff]
            simpa using h
          intro heq
          apply hnot
          rw [← heq]
          have hlt : k + 1 < (b :: l).length := by simp; omega
          rw [List.getD_eq_getElem _ _ hlt]
          exact List.getElem_mem hlt
        · exact ih b hnd'.2 k w (by simp; omega) hw hne
    · have hab' : a = b := by simpa using hab
      subst hab'
      rw [List.destutter'_cons_neg (l := l) hab] at hnd
      cases k with
      | zero =>
        simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hw
        simp only [List.getD_cons_zero] at hne
        exact absurd hw.symm hne
      | succ k =>
        rw [List.take_succ_cons, List.mem_cons] at hw
        simp only [List.length_cons] at hk
        rw [List.getD_cons_succ] at hne ⊢
        have hk' : k + 1 < (a :: l).length := by simp; omega
        rcases hw with rfl | hw
        · exact ih _ hnd k _ hk' (by simp) hne
        · exact ih a hnd k w hk' hw hne

theorem destutter_noReturn {l : List Nat} (hnd : (l.destutter (· ≠ ·)).Nodup) {k w : Nat}
    (hk : k + 1 < l.length) (hw : w ∈ l.take (k + 1)) (hne : l.getD k 0 ≠ w) :
    l.getD (k + 1) 0 ≠ w := by
  cases l with
  | nil => simp at hk
  | cons a l =>
    rw [List.destutter_cons'] at hnd
    exact destutter'_noReturn l a hnd k w hk hw hne

end FamTrans6

open FamTrans6

/-! ## L5.9: no-revisit semantics -/

theorem noRevisit_sem {S : List (List Nat)} (hL : Legal S) {t m w : Nat} (hm : m < 6)
    (ht : t < S.length) (hnew : (frame S (t + 1)).getD m 0 = w)
    (hold : (frame S t).getD m 0 ≠ w) : vis S t m w = false := by
  have hnd : ((colM S m).destutter (· ≠ ·)).Nodup := hL.2.1 m hm
  have hk : t + 1 < (colM S m).length := by rw [colM_length]; omega
  have hne : (colM S m).getD t 0 ≠ w := by rw [colM_getD (by omega)]; exact hold
  unfold vis
  rw [decide_eq_false_iff_not]
  intro hw
  apply destutter_noReturn hnd hk hw hne
  rw [colM_getD (by omega)]
  exact hnew

/-! ## The four blocks of `transitionClauses` at frame `t` -/

section Blocks

variable {k : Nat} {S : List (List Nat)} {idxs : List Nat}

/-- Stop-copy clauses `[-S[t][0], -M[t][m][w], M[t+1][m][w]]`. -/
theorem stopTrans_sat {t : Nat} (ht : t < 15) :
    ((List.range 6).flatMap fun m =>
      (List.range 6).map fun w =>
        [neg (sVar (layout 6) t 0), neg (mVar (layout 6) t m w),
          pos (mVar (layout 6) (t + 1) m w)]).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨m, hm, w, hw, rfl⟩ := hc
  rw [evalClause3, evalLit_neg6 _ (sVar_pos _ _ _), evalLit_neg6 _ (mVar_pos _ _ _ _),
    evalLit_pos6 _ (mVar_pos _ _ _ _), tau_S S idxs t 0 ht (by omega),
    tau_M S idxs t m w (by omega) hm hw, tau_M S idxs (t + 1) m w (by omega) hm hw]
  by_cases h0 : 0 = stepIdx S t
  · have hle : S.length ≤ t := by
      by_contra hlt
      have := (stepIdx_pos_iff S t).2 (Nat.lt_of_not_le hlt)
      omega
    rw [frame_succ_stop hle]
    cases decide ((frame S t).getD m 0 = w) <;> simp
  · simp [h0]

/-- The shape clauses of one shape `sh` at frame `t` with step index `j`,
under the only fact the proof needs about `sh`: if `S[t][j]` is true then
`t < S.length` and `sh` is the (min-first) step taken at `t`. -/
theorem shapeClauses_sat_of {t j : Nat} (ht : t < 15) (hj : j ≤ 409) (sh : List Nat)
    (hsh : j = stepIdx S t → t < S.length ∧ WFStep (S.getD t []) ∧
      sh = minFirst (S.getD t [])) :
    (shapeClauses (layout 6) t j sh).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [shapeClauses, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_map] at hc
  by_cases hs : j = stepIdx S t
  · obtain ⟨htlen, hWFst, hshape⟩ := hsh hs
    have hWFsh : WFStep sh := hshape ▸ minFirst_WFStep hWFst
    have hframe : frame S (t + 1) = applyStep sh (frame S t) := by
      rw [frame_succ_step htlen, hshape, applyStep_minFirst hWFst]
    obtain ⟨h2, hnd, hlt6⟩ := hWFsh
    rcases hc with ⟨i, hi, w, hw, rfl⟩ | ⟨m, hm, hc⟩
    · -- cycle clause: `sh[i]` takes the wife of `sh[(i+1) % kk]`
      have hlt_i : i < sh.length := hi
      have ha_mem : sh.getD i 0 ∈ sh := by
        rw [List.getD_eq_getElem _ _ hlt_i]; exact List.getElem_mem hlt_i
      have hb_pos : (i + 1) % sh.length < sh.length := step_succ_pos_lt h2
      have hb_mem : sh.getD ((i + 1) % sh.length) 0 ∈ sh := by
        rw [List.getD_eq_getElem _ _ hb_pos]; exact List.getElem_mem hb_pos
      have ha6 : sh.getD i 0 < 6 := hlt6 _ ha_mem
      have hb6 : sh.getD ((i + 1) % sh.length) 0 < 6 := hlt6 _ hb_mem
      have hidx : idxOf (sh.getD i 0) sh = i := idxOf_getD hnd hlt_i
      have key : (frame S (t + 1)).getD (sh.getD i 0) 0 =
          (frame S t).getD (sh.getD ((i + 1) % sh.length) 0) 0 := by
        rw [hframe, applyStep_getD ha6, if_pos ha_mem, hidx]
      rw [evalClause3, evalLit_neg6 _ (sVar_pos _ _ _), evalLit_neg6 _ (mVar_pos _ _ _ _),
        evalLit_pos6 _ (mVar_pos _ _ _ _), tau_S S idxs t j ht hj,
        tau_M S idxs t _ w (by omega) hb6 hw, tau_M S idxs (t + 1) _ w (by omega) ha6 hw, key]
      cases decide ((frame S t).getD (sh.getD ((i + 1) % sh.length) 0) 0 = w) <;> simp
    · -- a man outside the shape keeps his wife
      split at hc
      · exact absurd hc List.not_mem_nil
      · next hcm =>
        have hnm : m ∉ sh := fun hmem => hcm (List.contains_iff_mem.2 hmem)
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨w, hw, rfl⟩ := hc
        have key : (frame S (t + 1)).getD m 0 = (frame S t).getD m 0 := by
          rw [hframe, applyStep_getD hm, if_neg hnm]
        rw [evalClause3, evalLit_neg6 _ (sVar_pos _ _ _), evalLit_neg6 _ (mVar_pos _ _ _ _),
          evalLit_pos6 _ (mVar_pos _ _ _ _), tau_S S idxs t j ht hj,
          tau_M S idxs t m w (by omega) hm hw, tau_M S idxs (t + 1) m w (by omega) hm hw, key]
        cases decide ((frame S t).getD m 0 = w) <;> simp
  · -- the step literal `-S[t][j]` is true
    have hlit : evalLit (tau6 k S idxs) (neg (sVar (layout 6) t j)) = true := by
      rw [evalLit_neg6 _ (sVar_pos _ _ _), tau_S S idxs t j ht hj]
      simp [hs]
    rcases hc with ⟨i, hi, w, hw, rfl⟩ | ⟨m, hm, hc⟩
    · simp [evalClause, hlit]
    · split at hc
      · exact absurd hc List.not_mem_nil
      · simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨w, hw, rfl⟩ := hc
        simp [evalClause, hlit]

/-- The shape clauses of shape `j' < 409` at frame `t`. -/
theorem shapeClauses_sat (hL : Legal S) {t : Nat} (ht : t < 15) {j' : Nat} (hj : j' < 409) :
    (shapeClauses (layout 6) t (j' + 1) ((cyclicShapes 6).getD j' [])).all
      (evalClause (tau6 k S idxs)) = true := by
  apply shapeClauses_sat_of ht (by omega)
  intro hs
  have htlen : t < S.length := (stepIdx_pos_iff S t).1 (by omega)
  have hWFst : WFStep (S.getD t []) := by
    apply hL.1
    rw [List.getD_eq_getElem _ _ htlen]
    exact List.getElem_mem htlen
  refine ⟨htlen, hWFst, ?_⟩
  have h := shape_of_stepIdx hL.1 htlen
  have hj' : stepIdx S t - 1 = j' := by omega
  rw [hj'] at h
  exact h

/-- No-revisit clauses `[-M[t+1][m][w], M[t][m][w], -V[t][m][w]]`. -/
theorem noRevisit_sat (hL : Legal S) {t : Nat} (ht : t < 15) :
    ((List.range 6).flatMap fun m =>
      (List.range 6).map fun w =>
        [neg (mVar (layout 6) (t + 1) m w), pos (mVar (layout 6) t m w),
          neg (vVar (layout 6) t m w)]).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨m, hm, w, hw, rfl⟩ := hc
  rw [evalClause3, evalLit_neg6 _ (mVar_pos _ _ _ _), evalLit_pos6 _ (mVar_pos _ _ _ _),
    evalLit_neg6 _ (vVar_pos _ _ _ _), tau_M S idxs (t + 1) m w (by omega) hm hw,
    tau_M S idxs t m w (by omega) hm hw, tau_V S idxs t m w (by omega) hm hw]
  by_cases htl : t < S.length
  · by_cases hnew : (frame S (t + 1)).getD m 0 = w
    · by_cases hold : (frame S t).getD m 0 = w
      · rw [decide_eq_true hold]; simp
      · rw [noRevisit_sem hL hm htl hnew hold]; simp
    · rw [decide_eq_false hnew]; simp
  · rw [frame_succ_stop (Nat.le_of_not_lt htl)]
    cases decide ((frame S t).getD m 0 = w) <;> simp

/-- Visited-update clauses `V[t+1] ↔ V[t] ∨ M[t+1]`. -/
theorem visUpdate_sat {t : Nat} (ht : t < 15) :
    ((List.range 6).flatMap fun m =>
      (List.range 6).flatMap fun w =>
        [[neg (vVar (layout 6) t m w), pos (vVar (layout 6) (t + 1) m w)],
         [neg (mVar (layout 6) (t + 1) m w), pos (vVar (layout 6) (t + 1) m w)],
         [neg (vVar (layout 6) (t + 1) m w), pos (vVar (layout 6) t m w),
           pos (mVar (layout 6) (t + 1) m w)]]).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨m, hm, w, hw, hc⟩ := hc
  have hvs := vis_succ (S := S) t m w
  rcases hc with rfl | rfl | rfl
  · rw [evalClause2, evalLit_neg6 _ (vVar_pos _ _ _ _), evalLit_pos6 _ (vVar_pos _ _ _ _),
      tau_V S idxs t m w (by omega) hm hw, tau_V S idxs (t + 1) m w (by omega) hm hw, hvs]
    cases vis S t m w <;> simp
  · rw [evalClause2, evalLit_neg6 _ (mVar_pos _ _ _ _), evalLit_pos6 _ (vVar_pos _ _ _ _),
      tau_M S idxs (t + 1) m w (by omega) hm hw, tau_V S idxs (t + 1) m w (by omega) hm hw, hvs]
    cases decide ((frame S (t + 1)).getD m 0 = w) <;> simp
  · rw [evalClause3, evalLit_neg6 _ (vVar_pos _ _ _ _), evalLit_pos6 _ (vVar_pos _ _ _ _),
      evalLit_pos6 _ (mVar_pos _ _ _ _), tau_V S idxs (t + 1) m w (by omega) hm hw,
      tau_V S idxs t m w (by omega) hm hw, tau_M S idxs (t + 1) m w (by omega) hm hw, hvs]
    cases vis S t m w <;> cases decide ((frame S (t + 1)).getD m 0 = w) <;> simp

/-! ## Family 4 assembled -/

set_option linter.unusedVariables false in
theorem transition_sat (hL : Legal S) (hlen : S.length ≤ 15) :
    (transitionClauses (layout 6) (cyclicShapes 6)).all (evalClause (tau6 k S idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  unfold transitionClauses at hc
  obtain ⟨t, ht, hc⟩ := List.mem_flatMap.1 hc
  rw [List.mem_range, layout6_F] at ht
  simp only [layout6_n] at hc
  rcases List.mem_append.1 hc with hc | hc
  · rcases List.mem_append.1 hc with hc | hc
    · rcases List.mem_append.1 hc with hc | hc
      · exact List.all_eq_true.1 (stopTrans_sat ht) c hc
      · obtain ⟨j', hj, hc⟩ := List.mem_flatMap.1 hc
        rw [List.mem_range, cyclicShapes6_length] at hj
        exact List.all_eq_true.1 (shapeClauses_sat hL ht hj) c hc
    · exact List.all_eq_true.1 (noRevisit_sat hL ht) c hc
  · exact List.all_eq_true.1 (visUpdate_sat ht) c hc

end Blocks
