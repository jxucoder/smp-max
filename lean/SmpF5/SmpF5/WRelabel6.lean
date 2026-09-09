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

/-! ## Normalizing the man-optimal matching to the identity -/

theorem idRow6_getD6 {i : Nat} (hi : i < 6) : idRow6.getD i 0 = i := by
  rw [idRow6_eq_range]
  have hlt : i < (List.range 6).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_range]

/-- Transport of stable-matching membership along `μ ↦ μ.map (app σ)`. -/
theorem mem_sms6_wmap_iff {σ : List Nat} (hp : σ.Perm idRow6) {I : Inst6}
    {mu : List Nat} (hmu : mu.Perm idRow6) :
    mu.map (app σ) ∈ sms6 (wrelabel6 σ I) ↔ mu ∈ sms6 I := by
  unfold sms6
  rw [List.mem_filter, List.mem_filter, List.mem_permutations,
    List.mem_permutations, isStable6_wrelabel6 hp hmu]
  exact ⟨fun h => ⟨hmu, h.2⟩, fun h => ⟨wmap_perm hp hmu, h.2⟩⟩

/-- Stable matchings of the relabeled instance, pulled back to `I`. -/
theorem mem_sms6_wrelabel6_iff {σ : List Nat} (hp : σ.Perm idRow6) {I : Inst6}
    {nu : List Nat} (hnu : nu.Perm idRow6) :
    nu ∈ sms6 (wrelabel6 σ I) ↔ nu.map (app (invMatch σ)) ∈ sms6 I := by
  have hnu' : (nu.map (app (invMatch σ))).Perm idRow6 :=
    wmap_perm (invMatch_perm hp) hnu
  have h := mem_sms6_wmap_iff hp (I := I) hnu'
  rw [map_app_right_inv6 hp hnu] at h
  exact h

theorem manOpt_wrelabel6_aux {I : Inst6} (hWF : WF6 I = true)
    (hne : sms6 I ≠ []) {μ0 σ : List Nat} (hμ0 : μ0 = manOpt I)
    (hσ : σ = invMatch μ0) : manOpt (wrelabel6 σ I) = idRow6 := by
  obtain ⟨hμ0mem, hdom⟩ := manOpt_spec hWF hne
  rw [← hμ0] at hμ0mem hdom
  have hpμ0 : μ0.Perm idRow6 := mem_sms6_perm hμ0mem
  have hp : σ.Perm idRow6 := by rw [hσ]; exact invMatch_perm hpμ0
  have hinv : invMatch σ = μ0 := by rw [hσ]; exact invMatch_invMatch hpμ0
  -- Step 1: μ0 is sent to the identity.
  have hid : μ0.map (app σ) = idRow6 := by
    apply List.ext_getElem
    · rw [List.length_map, perm6_length hpμ0]; rfl
    · intro i h1 h2
      have hi : i < 6 := by
        rw [List.length_map, perm6_length hpμ0] at h1; exact h1
      rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2,
        wmap_getD hpμ0 hi, idRow6_getD6 hi]
      have hpart : μ0.getD i 0 < 6 := perm6_getD_lt hpμ0 hi
      change σ.getD (μ0.getD i 0) 0 = i
      rw [hσ, invMatch_getD hpart, partner_idxOf hpμ0 hi]
  -- Step 2: the identity is stable in the relabeled instance.
  have hidJ : idRow6 ∈ sms6 (wrelabel6 σ I) := by
    rw [← hid]
    exact (mem_sms6_wmap_iff hp hpμ0).2 hμ0mem
  -- Step 3: the identity dominates every stable matching of `J`.
  have hbest : ∀ ν ∈ sms6 (wrelabel6 σ I), ∀ m, m < 6 →
      get2 (wrelabel6 σ I).mrank m (idRow6.getD m 0) ≤
        get2 (wrelabel6 σ I).mrank m (ν.getD m 0) := by
    intro ν hν m hm
    have hpν : ν.Perm idRow6 := mem_sms6_perm hν
    have hν' : ν.map (app (invMatch σ)) ∈ sms6 I :=
      (mem_sms6_wrelabel6_iff hp hpν).1 hν
    have hνm : ν.getD m 0 < 6 := perm6_getD_lt hpν hm
    have e1 : get2 (wrelabel6 σ I).mrank m (idRow6.getD m 0)
        = get2 I.mrank m (μ0.getD m 0) := by
      rw [idRow6_getD6 hm, get2_wrelabel6_m hm hm]
      change get2 I.mrank m ((invMatch σ).getD m 0) = _
      rw [hinv]
    have e2 : get2 (wrelabel6 σ I).mrank m (ν.getD m 0)
        = get2 I.mrank m ((ν.map (app (invMatch σ))).getD m 0) := by
      rw [get2_wrelabel6_m hm hνm, wmap_getD hpν hm]
    rw [e1, e2]
    exact hdom _ hν' m hm
  -- Step 4: antisymmetry of dominance.
  have hneJ : sms6 (wrelabel6 σ I) ≠ [] := by
    intro h
    rw [h] at hidJ
    simp at hidJ
  have hWFJ : WF6 (wrelabel6 σ I) = true := WF6_wrelabel6 hp hWF
  obtain ⟨hmoJ, hdomJ⟩ := manOpt_spec hWFJ hneJ
  exact dominance_antisymm hWFJ hmoJ hidJ (hdomJ _ hidJ) (hbest _ hmoJ)

theorem manOpt_wrelabel6 {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ []) :
    manOpt (wrelabel6 (invMatch (manOpt I)) I) = idRow6 :=
  manOpt_wrelabel6_aux hWF hne rfl rfl

/-! ## The Validity Lemma, unconditionally -/

theorem Legal_nil : Legal [] := by
  refine ⟨fun st hst => absurd hst (by simp), ?_, ?_⟩
  · intro m _
    simp [strajM, schedMatchings]
  · intro w _
    simp [strajW, schedMatchings]

theorem validity_unconditional {I : Inst6} (hWF : WF6 I = true) :
    ∃ S : List (List Nat), Legal S ∧ stableCount6 I ≤ stableCount6 (readoffS S) := by
  by_cases hne : sms6 I = []
  · refine ⟨[], Legal_nil, ?_⟩
    have h0 : stableCount6 I = 0 := by simp [stableCount6, hne]
    rw [h0]
    exact Nat.zero_le _
  · have hμ0 : manOpt I ∈ sms6 I := (manOpt_spec hWF hne).1
    have hp : (invMatch (manOpt I)).Perm idRow6 :=
      invMatch_perm (mem_sms6_perm hμ0)
    have hWFJ : WF6 (wrelabel6 (invMatch (manOpt I)) I) = true :=
      WF6_wrelabel6 hp hWF
    have hmo : manOpt (wrelabel6 (invMatch (manOpt I)) I) = idRow6 :=
      manOpt_wrelabel6 hWF hne
    have hcnt : stableCount6 (wrelabel6 (invMatch (manOpt I)) I) = stableCount6 I :=
      stableCount6_wrelabel6 hp I
    have hneJ : sms6 (wrelabel6 (invMatch (manOpt I)) I) ≠ [] := by
      intro h
      have h1 : (sms6 I).length = 0 := by
        have h2 := hcnt
        unfold stableCount6 at h2
        rw [h] at h2
        exact h2.symm
      exact hne (List.eq_nil_of_length_eq_zero h1)
    refine ⟨chainSched (wrelabel6 (invMatch (manOpt I)) I),
      Legal_chainSched hWFJ hneJ hmo, ?_⟩
    rw [← hcnt]
    exact sc_le_readoffS_chainSched hWFJ hneJ hmo
