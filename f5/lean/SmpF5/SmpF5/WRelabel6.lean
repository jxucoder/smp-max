import SmpF5.ValidityBridge6

/-!
# Women-only relabeling (normalizing the man-optimal matching)

`wrelabel6 σ I` renames woman `w` to `app σ w` and leaves men fixed. A
matching `μ` of `I` becomes `μ.map (app σ)`. Choosing `σ = invMatch
(manOpt I)` sends the man-optimal matching to the identity, which is the
precondition of `sc_le_readoffS_chainSched`. The stable-matching count is
invariant, so the Validity Lemma follows unconditionally.
-/

def wrelabel6 (σ : List Nat) (I : Inst6) : Inst6 where
  mrank := (List.range 6).map fun m => (List.range 6).map fun w' =>
    get2 I.mrank m (app (invMatch σ) w')
  wrank := (List.range 6).map fun w' => (List.range 6).map fun m =>
    get2 I.wrank (app (invMatch σ) w') m

theorem get2_wrelabel6_m {σ : List Nat} {I : Inst6} {m w : Nat}
    (hm : m < 6) (hw : w < 6) :
    get2 (wrelabel6 σ I).mrank m w = get2 I.mrank m (app (invMatch σ) w) := by
  show ((wrelabel6 σ I).mrank.getD m []).getD w 0 = _
  unfold wrelabel6
  rw [getD_map_range6 hm, getD_map_range6 hw]

theorem get2_wrelabel6_w {σ : List Nat} {I : Inst6} {w m : Nat}
    (hw : w < 6) (hm : m < 6) :
    get2 (wrelabel6 σ I).wrank w m = get2 I.wrank (app (invMatch σ) w) m := by
  show ((wrelabel6 σ I).wrank.getD w []).getD m 0 = _
  unfold wrelabel6
  rw [getD_map_range6 hw, getD_map_range6 hm]

theorem WF6_wrelabel6 {σ : List Nat} (hp : σ.Perm idRow6) {I : Inst6}
    (h : WF6 I = true) : WF6 (wrelabel6 σ I) = true := by
  obtain ⟨hml, hmrows⟩ := mrank_facts h
  obtain ⟨hwl, hwrows⟩ := wrank_facts h
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨by simp [wrelabel6], by simp [wrelabel6]⟩, ?_⟩, ?_⟩
  · intro r hr
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hr
    have hm6 : m < 6 := by simpa using hm
    have hrow : isRankRow6 (I.mrank.getD m []) = true := by
      have hi : m < I.mrank.length := by rw [hml]; exact hm6
      rw [List.getD_eq_getElem _ _ hi]
      exact hmrows _ (List.getElem_mem hi)
    exact isRankRow6_reindex hp hrow
  · intro r hr
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hr
    have hw'6 : w' < 6 := by simpa using hw'
    have hi : app (invMatch σ) w' < I.wrank.length := by
      rw [hwl]; exact inv_app_lt6 hp hw'6
    have hrow : isRankRow6 (I.wrank.getD (app (invMatch σ) w') []) = true := by
      rw [List.getD_eq_getElem _ _ hi]
      exact hwrows _ (List.getElem_mem hi)
    -- the row is a literal copy of the old row
    have hcopy : ((List.range 6).map fun m =>
        get2 I.wrank (app (invMatch σ) w') m)
        = I.wrank.getD (app (invMatch σ) w') [] := by
      have hlen : (I.wrank.getD (app (invMatch σ) w') []).length = 6 :=
        perm6_length (rankRow6_perm hrow)
      apply List.ext_getElem
      · rw [List.length_map, List.length_range, hlen]
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        show ((I.wrank.getD (app (invMatch σ) w') []).getD i 0) = _
        rw [List.getD_eq_getElem _ _ h2]
    rw [hcopy]
    exact hrow

/-! ## Matching transport `μ ↦ μ.map (app σ)` -/

theorem wmap_getD {σ mu : List Nat} (hmu : mu.Perm idRow6) {m : Nat}
    (hm : m < 6) : (mu.map (app σ)).getD m 0 = app σ (mu.getD m 0) := by
  have h : m < mu.length := by rw [perm6_length hmu]; exact hm
  exact getD_map_nat h

theorem wmap_perm {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu.Perm idRow6) : (mu.map (app σ)).Perm idRow6 := by
  have h1 : (mu.map (app σ)).Perm (idRow6.map (app σ)) := hmu.map _
  rw [map_app_idRow6 hp] at h1
  exact h1.trans hp

theorem wmap_idxOf {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu.Perm idRow6) {w : Nat} (hw : w < 6) :
    idxOf w (mu.map (app σ)) = idxOf (app (invMatch σ) w) mu := by
  have hwi : app (invMatch σ) w < 6 := inv_app_lt6 hp hw
  have hwm : app (invMatch σ) w ∈ mu := perm6_mem hmu hwi
  have hplt : idxOf (app (invMatch σ) w) mu < 6 := by
    have := idxOf_lt_length hwm
    rwa [perm6_length hmu] at this
  refine partner_idxOf_of_eq (wmap_perm hp hmu) hplt ?_
  rw [wmap_getD hmu hplt]
  show app σ (mu.getD (idxOf (app (invMatch σ) w) mu) 0) = w
  rw [getD_idxOf hwm]
  exact app_inv_app6 hp hw

theorem isStable6_wrelabel6 {σ : List Nat} (hp : σ.Perm idRow6)
    {I : Inst6} {mu : List Nat} (hmu : mu.Perm idRow6) :
    isStable6 (wrelabel6 σ I) (mu.map (app σ)) = isStable6 I mu := by
  rw [Bool.eq_iff_iff]
  simp only [isStable6, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · intro H m hm w hw
    have hσw : app σ w < 6 := app_lt6 hp hw
    have hpart : mu.getD m 0 < 6 := perm6_getD_lt hmu hm
    have hidx : idxOf w mu < 6 := by
      have := idxOf_lt_length (perm6_mem hmu hw)
      rwa [perm6_length hmu] at this
    have hinvw : app (invMatch σ) (app σ w) = w := inv_app_app6 hp hw
    have hgd : (mu.map (app σ)).getD m 0 = app σ (mu.getD m 0) := wmap_getD hmu hm
    have hix : idxOf (app σ w) (mu.map (app σ)) = idxOf w mu := by
      rw [wmap_idxOf hp hmu hσw, hinvw]
    have e1 : get2 (wrelabel6 σ I).mrank m (app σ w) = get2 I.mrank m w := by
      rw [get2_wrelabel6_m hm hσw, hinvw]
    have e2 : get2 (wrelabel6 σ I).mrank m ((mu.map (app σ)).getD m 0)
        = get2 I.mrank m (mu.getD m 0) := by
      rw [hgd, get2_wrelabel6_m hm (app_lt6 hp hpart), inv_app_app6 hp hpart]
    have e4 : get2 (wrelabel6 σ I).wrank (app σ w) m = get2 I.wrank w m := by
      rw [get2_wrelabel6_w hσw hm, hinvw]
    have e5 : get2 (wrelabel6 σ I).wrank (app σ w)
          (idxOf (app σ w) (mu.map (app σ)))
        = get2 I.wrank w (idxOf w mu) := by
      rw [hix, get2_wrelabel6_w hσw hidx, hinvw]
    rcases H m hm (app σ w) hσw with h1 | h2 | h2
    · left
      rw [hgd] at h1
      exact app_inj6 hp hw hpart h1
    · right; left
      rw [e1, e2] at h2
      exact h2
    · right; right
      rw [e4, e5] at h2
      exact h2
  · intro H m hm w' hw'
    have hw : app (invMatch σ) w' < 6 := inv_app_lt6 hp hw'
    have hpart : mu.getD m 0 < 6 := perm6_getD_lt hmu hm
    have hidx : idxOf (app (invMatch σ) w') mu < 6 := by
      have := idxOf_lt_length (perm6_mem hmu hw)
      rwa [perm6_length hmu] at this
    have hgd : (mu.map (app σ)).getD m 0 = app σ (mu.getD m 0) := wmap_getD hmu hm
    have hix : idxOf w' (mu.map (app σ)) = idxOf (app (invMatch σ) w') mu :=
      wmap_idxOf hp hmu hw'
    have e1 : get2 (wrelabel6 σ I).mrank m w'
        = get2 I.mrank m (app (invMatch σ) w') := get2_wrelabel6_m hm hw'
    have e2 : get2 (wrelabel6 σ I).mrank m ((mu.map (app σ)).getD m 0)
        = get2 I.mrank m (mu.getD m 0) := by
      rw [hgd, get2_wrelabel6_m hm (app_lt6 hp hpart), inv_app_app6 hp hpart]
    have e4 : get2 (wrelabel6 σ I).wrank w' m
        = get2 I.wrank (app (invMatch σ) w') m := get2_wrelabel6_w hw' hm
    have e5 : get2 (wrelabel6 σ I).wrank w' (idxOf w' (mu.map (app σ)))
        = get2 I.wrank (app (invMatch σ) w') (idxOf (app (invMatch σ) w') mu) := by
      rw [hix, get2_wrelabel6_w hw' hidx]
    rcases H m hm (app (invMatch σ) w') hw with h1 | h2 | h2
    · left
      rw [hgd, ← h1]
      exact (app_inv_app6 hp hw').symm
    · right; left
      rw [e1, e2]
      exact h2
    · right; right
      rw [e4, e5]
      exact h2

/-! ## Count invariance -/

theorem wmap_left_inv {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu.Perm idRow6) :
    (mu.map (app σ)).map (app (invMatch σ)) = mu :=
  map_app_left_inv6 hp hmu

theorem perms_wmap_perm {σ : List Nat} (hp : σ.Perm idRow6) :
    (idRow6.permutations.map (fun mu => mu.map (app σ))).Perm
      idRow6.permutations :=
  perms_map_perm6 hp

theorem stableCount6_wrelabel6 {σ : List Nat} (hp : σ.Perm idRow6)
    (I : Inst6) :
    stableCount6 (wrelabel6 σ I) = stableCount6 I := by
  unfold stableCount6 sms6
  have hperm := perms_wmap_perm (σ := σ) hp
  have h1 := (hperm.filter (isStable6 (wrelabel6 σ I))).length_eq
  rw [← h1, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro mu hmu
  show isStable6 (wrelabel6 σ I) (mu.map (app σ)) = isStable6 I mu
  exact isStable6_wrelabel6 hp (List.mem_permutations.1 hmu)
