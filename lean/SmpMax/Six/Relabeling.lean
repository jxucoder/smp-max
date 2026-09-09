import SmpMax.Six.Chains

/-!
# Order-6 relabeling invariance (Lemma sym (ii))

Relabel men and women by the *same* permutation `σ` (old label `x` gets
new label `app σ x`). The identity matching is preserved, schedules map
to schedules, and the stable-matching count is invariant — the fact the
cube campaign's first-appearance normalization rests on.

`invMatch σ` (from `Lattice6`) is the inverse permutation list, so the
whole inverse theory is inherited.
-/

theorem inv_app_app6 {σ : List Nat} (hp : σ.Perm idRow6) {w : Nat}
    (hw : w < 6) : app (invMatch σ) (app σ w) = w := by
  have hb : σ.getD w 0 < 6 := perm6_getD_lt hp hw
  show (invMatch σ).getD (σ.getD w 0) 0 = w
  rw [invMatch_getD hb]
  exact partner_idxOf hp hw

theorem app_inv_app6 {σ : List Nat} (hp : σ.Perm idRow6) {v : Nat}
    (hv : v < 6) : app σ (app (invMatch σ) v) = v := by
  show σ.getD ((invMatch σ).getD v 0) 0 = v
  rw [invMatch_getD hv]
  exact getD_idxOf (perm6_mem hp hv)

theorem app_lt6 {σ : List Nat} (hp : σ.Perm idRow6) {w : Nat}
    (hw : w < 6) : app σ w < 6 := perm6_getD_lt hp hw

theorem inv_app_lt6 {σ : List Nat} (hp : σ.Perm idRow6) {v : Nat}
    (hv : v < 6) : app (invMatch σ) v < 6 :=
  perm6_getD_lt (invMatch_perm hp) hv

theorem map_app_left_inv6 {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu.Perm idRow6) :
    (mu.map (app σ)).map (app (invMatch σ)) = mu := by
  rw [List.map_map]
  have hc : ∀ x ∈ mu, (app (invMatch σ) ∘ app σ) x = id x := by
    intro x hx
    simpa using inv_app_app6 hp (perm6_entry_lt hmu hx)
  rw [List.map_congr_left hc, List.map_id]

theorem map_app_right_inv6 {σ mu' : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu'.Perm idRow6) :
    (mu'.map (app (invMatch σ))).map (app σ) = mu' := by
  rw [List.map_map]
  have hc : ∀ x ∈ mu', (app σ ∘ app (invMatch σ)) x = id x := by
    intro x hx
    simpa using app_inv_app6 hp (perm6_entry_lt hmu hx)
  rw [List.map_congr_left hc, List.map_id]

theorem idRow6_eq_range : idRow6 = List.range 6 := by decide

theorem map_app_idRow6 {σ : List Nat} (hp : σ.Perm idRow6) :
    idRow6.map (app σ) = σ := by
  have hlen : σ.length = 6 := perm6_length hp
  rw [idRow6_eq_range]
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    show σ.getD i 0 = σ[i]
    rw [List.getD_eq_getElem _ _ (by omega)]

theorem mapMu_mem6 {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu ∈ idRow6.permutations) :
    mu.map (app σ) ∈ idRow6.permutations := by
  have hmup : mu.Perm idRow6 := List.mem_permutations.1 hmu
  apply List.mem_permutations.2
  have h1 : (mu.map (app σ)).Perm (idRow6.map (app σ)) := hmup.map _
  rw [map_app_idRow6 hp] at h1
  exact h1.trans hp

theorem perms_map_perm6 {σ : List Nat} (hp : σ.Perm idRow6) :
    (idRow6.permutations.map (fun mu => mu.map (app σ))).Perm
      idRow6.permutations := by
  have hnd : idRow6.permutations.Nodup :=
    List.nodup_permutations _ (by decide)
  have hndm : (idRow6.permutations.map
      (fun mu => mu.map (app σ))).Nodup := by
    refine List.Nodup.map_on ?_ hnd
    intro mu1 h1 mu2 h2 heq
    have hc := congrArg (List.map (app (invMatch σ))) heq
    rwa [map_app_left_inv6 hp (List.mem_permutations.1 h1),
        map_app_left_inv6 hp (List.mem_permutations.1 h2)] at hc
  rw [List.perm_ext_iff_of_nodup hndm hnd]
  intro mu'
  constructor
  · intro hmem
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hmem
    exact mapMu_mem6 hp hmu
  · intro hmem
    refine List.mem_map.2 ⟨mu'.map (app (invMatch σ)), ?_, ?_⟩
    · exact mapMu_mem6 (invMatch_perm hp) hmem
    · exact map_app_right_inv6 hp (List.mem_permutations.1 hmem)

/-! ## The relabeled instance -/

def relabel6 (σ : List Nat) (I : Inst6) : Inst6 where
  mrank := (List.range 6).map fun m' => (List.range 6).map fun w' =>
    get2 I.mrank (app (invMatch σ) m') (app (invMatch σ) w')
  wrank := (List.range 6).map fun w' => (List.range 6).map fun m' =>
    get2 I.wrank (app (invMatch σ) w') (app (invMatch σ) m')

theorem get2_relabel6_m {σ : List Nat} {I : Inst6} {m w : Nat}
    (hm : m < 6) (hw : w < 6) :
    get2 (relabel6 σ I).mrank m w
      = get2 I.mrank (app (invMatch σ) m) (app (invMatch σ) w) := by
  show ((relabel6 σ I).mrank.getD m []).getD w 0 = _
  unfold relabel6
  rw [getD_map_range6 hm, getD_map_range6 hw]

theorem get2_relabel6_w {σ : List Nat} {I : Inst6} {w m : Nat}
    (hw : w < 6) (hm : m < 6) :
    get2 (relabel6 σ I).wrank w m
      = get2 I.wrank (app (invMatch σ) w) (app (invMatch σ) m) := by
  show ((relabel6 σ I).wrank.getD w []).getD m 0 = _
  unfold relabel6
  rw [getD_map_range6 hw, getD_map_range6 hm]

theorem isRankRow6_reindex {σ : List Nat} (hp : σ.Perm idRow6)
    {row : List Nat} (hr : isRankRow6 row = true) :
    isRankRow6 ((List.range 6).map fun w' =>
      row.getD (app (invMatch σ) w') 0) = true := by
  have hrp : row.Perm idRow6 := rankRow6_perm hr
  simp only [isRankRow6, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  constructor
  · simp
  · intro v hv
    have hvmem : v ∈ row := perm6_mem hrp hv
    have hidx : idxOf v row < 6 := by
      have := idxOf_lt_length hvmem
      rwa [perm6_length hrp] at this
    rw [List.contains_iff_mem]
    refine List.mem_map.2 ⟨app σ (idxOf v row), ?_, ?_⟩
    · simp only [List.mem_range]
      exact app_lt6 hp hidx
    · rw [inv_app_app6 hp hidx]
      exact getD_idxOf hvmem

theorem WF6_relabel6 {σ : List Nat} (hp : σ.Perm idRow6) {I : Inst6}
    (h : WF6 I = true) : WF6 (relabel6 σ I) = true := by
  obtain ⟨hml, hmrows⟩ := mrank_facts h
  obtain ⟨hwl, hwrows⟩ := wrank_facts h
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨by simp [relabel6], by simp [relabel6]⟩, ?_⟩, ?_⟩
  · intro r hr
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hr
    have hm'6 : m' < 6 := by simpa using hm'
    have hrow : isRankRow6 (I.mrank.getD (app (invMatch σ) m') []) = true := by
      have hi : app (invMatch σ) m' < I.mrank.length := by
        rw [hml]; exact inv_app_lt6 hp hm'6
      rw [List.getD_eq_getElem _ _ hi]
      exact hmrows _ (List.getElem_mem hi)
    exact isRankRow6_reindex hp hrow
  · intro r hr
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hr
    have hw'6 : w' < 6 := by simpa using hw'
    have hrow : isRankRow6 (I.wrank.getD (app (invMatch σ) w') []) = true := by
      have hi : app (invMatch σ) w' < I.wrank.length := by
        rw [hwl]; exact inv_app_lt6 hp hw'6
      rw [List.getD_eq_getElem _ _ hi]
      exact hwrows _ (List.getElem_mem hi)
    exact isRankRow6_reindex hp hrow

/-! ## Matching transport: `mapMu6 σ mu = σ ∘ mu ∘ σ⁻¹` -/

def mapMu6 (σ mu : List Nat) : List Nat :=
  ((invMatch σ).map (app mu)).map (app σ)

theorem mapMu6_length {σ mu : List Nat} : (mapMu6 σ mu).length = 6 := by
  simp [mapMu6, invMatch]

theorem mapMu6_getD {σ mu : List Nat} {m : Nat} (hm : m < 6) :
    (mapMu6 σ mu).getD m 0 = app σ (app mu (app (invMatch σ) m)) := by
  unfold mapMu6
  have h2 : m < (invMatch σ).length := by simp [invMatch]; omega
  have h1 : m < ((invMatch σ).map (app mu)).length := by
    simpa using h2
  rw [getD_map_nat h1, getD_map_nat h2]
  rfl

theorem mapMu6_perm {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu.Perm idRow6) : (mapMu6 σ mu).Perm idRow6 := by
  unfold mapMu6
  have h1 : ((invMatch σ).map (app mu)).Perm (idRow6.map (app mu)) :=
    (invMatch_perm hp).map _
  rw [map_app_idRow6 hmu] at h1
  have h2 := h1.map (app σ)
  have h3 : (mu.map (app σ)).Perm (idRow6.map (app σ)) := hmu.map _
  rw [map_app_idRow6 hp] at h3
  exact h2.trans (h3.trans hp)

theorem mapMu6_idxOf {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu.Perm idRow6) {w : Nat} (hw : w < 6) :
    idxOf w (mapMu6 σ mu) = app σ (idxOf (app (invMatch σ) w) mu) := by
  have hwi : app (invMatch σ) w < 6 := inv_app_lt6 hp hw
  have hwm : app (invMatch σ) w ∈ mu := perm6_mem hmu hwi
  have hplt : idxOf (app (invMatch σ) w) mu < 6 := by
    have := idxOf_lt_length hwm
    rwa [perm6_length hmu] at this
  refine partner_idxOf_of_eq (mapMu6_perm hp hmu) (app_lt6 hp hplt) ?_
  rw [mapMu6_getD (app_lt6 hp hplt), inv_app_app6 hp hplt]
  show app σ (mu.getD (idxOf (app (invMatch σ) w) mu) 0) = w
  rw [getD_idxOf hwm]
  exact app_inv_app6 hp hw

theorem app_inj6 {σ : List Nat} (hp : σ.Perm idRow6) {a b : Nat}
    (ha : a < 6) (hb : b < 6) (h : app σ a = app σ b) : a = b := by
  have := congrArg (app (invMatch σ)) h
  rwa [inv_app_app6 hp ha, inv_app_app6 hp hb] at this

/-! ## Stability transport -/

theorem isStable6_relabel6 {σ : List Nat} (hp : σ.Perm idRow6)
    {I : Inst6} {mu : List Nat} (hmu : mu.Perm idRow6) :
    isStable6 (relabel6 σ I) (mapMu6 σ mu) = isStable6 I mu := by
  rw [Bool.eq_iff_iff]
  simp only [isStable6, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · -- relabeled stable → original stable
    intro H m hm w hw
    have hσm : app σ m < 6 := app_lt6 hp hm
    have hσw : app σ w < 6 := app_lt6 hp hw
    have hpart : mu.getD m 0 < 6 := perm6_getD_lt hmu hm
    have hidx : idxOf w mu < 6 := by
      have := idxOf_lt_length (perm6_mem hmu hw)
      rwa [perm6_length hmu] at this
    have hinvm : app (invMatch σ) (app σ m) = m := inv_app_app6 hp hm
    have hinvw : app (invMatch σ) (app σ w) = w := inv_app_app6 hp hw
    have hgd : (mapMu6 σ mu).getD (app σ m) 0 = app σ (mu.getD m 0) := by
      rw [mapMu6_getD hσm, hinvm]
      rfl
    have hix : idxOf (app σ w) (mapMu6 σ mu) = app σ (idxOf w mu) := by
      rw [mapMu6_idxOf hp hmu hσw, hinvw]
    have e1 : get2 (relabel6 σ I).mrank (app σ m) (app σ w)
        = get2 I.mrank m w := by
      rw [get2_relabel6_m hσm hσw, hinvm, hinvw]
    have e2 : get2 (relabel6 σ I).mrank (app σ m)
          ((mapMu6 σ mu).getD (app σ m) 0)
        = get2 I.mrank m (mu.getD m 0) := by
      rw [hgd, get2_relabel6_m hσm (app_lt6 hp hpart), hinvm,
        inv_app_app6 hp hpart]
    have e4 : get2 (relabel6 σ I).wrank (app σ w) (app σ m)
        = get2 I.wrank w m := by
      rw [get2_relabel6_w hσw hσm, hinvw, hinvm]
    have e5 : get2 (relabel6 σ I).wrank (app σ w)
          (idxOf (app σ w) (mapMu6 σ mu))
        = get2 I.wrank w (idxOf w mu) := by
      rw [hix, get2_relabel6_w hσw (app_lt6 hp hidx), hinvw,
        inv_app_app6 hp hidx]
    rcases H (app σ m) hσm (app σ w) hσw with h1 | h2 | h2
    · left
      rw [hgd] at h1
      exact app_inj6 hp hw hpart h1
    · right; left
      rw [e1, e2] at h2
      exact h2
    · right; right
      rw [e4, e5] at h2
      exact h2
  · -- original stable → relabeled stable
    intro H m' hm' w' hw'
    have hm : app (invMatch σ) m' < 6 := inv_app_lt6 hp hm'
    have hw : app (invMatch σ) w' < 6 := inv_app_lt6 hp hw'
    have hpart : mu.getD (app (invMatch σ) m') 0 < 6 :=
      perm6_getD_lt hmu hm
    have hidx : idxOf (app (invMatch σ) w') mu < 6 := by
      have := idxOf_lt_length (perm6_mem hmu hw)
      rwa [perm6_length hmu] at this
    have hgd : (mapMu6 σ mu).getD m' 0
        = app σ (mu.getD (app (invMatch σ) m') 0) := mapMu6_getD hm'
    have hix : idxOf w' (mapMu6 σ mu)
        = app σ (idxOf (app (invMatch σ) w') mu) := mapMu6_idxOf hp hmu hw'
    have e1 : get2 (relabel6 σ I).mrank m' w'
        = get2 I.mrank (app (invMatch σ) m') (app (invMatch σ) w') :=
      get2_relabel6_m hm' hw'
    have e2 : get2 (relabel6 σ I).mrank m' ((mapMu6 σ mu).getD m' 0)
        = get2 I.mrank (app (invMatch σ) m')
            (mu.getD (app (invMatch σ) m') 0) := by
      rw [hgd, get2_relabel6_m hm' (app_lt6 hp hpart),
        inv_app_app6 hp hpart]
    have e4 : get2 (relabel6 σ I).wrank w' m'
        = get2 I.wrank (app (invMatch σ) w') (app (invMatch σ) m') :=
      get2_relabel6_w hw' hm'
    have e5 : get2 (relabel6 σ I).wrank w' (idxOf w' (mapMu6 σ mu))
        = get2 I.wrank (app (invMatch σ) w')
            (idxOf (app (invMatch σ) w') mu) := by
      rw [hix, get2_relabel6_w hw' (app_lt6 hp hidx),
        inv_app_app6 hp hidx]
    rcases H (app (invMatch σ) m') hm (app (invMatch σ) w') hw
      with h1 | h2 | h2
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

theorem mapMu6_left_inv {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu.Perm idRow6) :
    mapMu6 (invMatch σ) (mapMu6 σ mu) = mu := by
  apply List.ext_getElem
  · rw [mapMu6_length, perm6_length hmu]
  · intro i h1 h2
    have hi6 : i < 6 := by rwa [mapMu6_length] at h1
    rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
    rw [mapMu6_getD hi6, invMatch_invMatch hp]
    show app (invMatch σ) ((mapMu6 σ mu).getD (app σ i) 0) = mu.getD i 0
    rw [mapMu6_getD (app_lt6 hp hi6), inv_app_app6 hp hi6]
    exact inv_app_app6 hp (perm6_getD_lt hmu hi6)

theorem mapMu6_mem_perms {σ mu : List Nat} (hp : σ.Perm idRow6)
    (hmu : mu ∈ idRow6.permutations) :
    mapMu6 σ mu ∈ idRow6.permutations :=
  List.mem_permutations.2 (mapMu6_perm hp (List.mem_permutations.1 hmu))

theorem perms_mapMu6_perm {σ : List Nat} (hp : σ.Perm idRow6) :
    (idRow6.permutations.map (mapMu6 σ)).Perm idRow6.permutations := by
  have hnd : idRow6.permutations.Nodup :=
    List.nodup_permutations _ (by decide)
  have hndm : (idRow6.permutations.map (mapMu6 σ)).Nodup := by
    refine List.Nodup.map_on ?_ hnd
    intro mu1 h1 mu2 h2 heq
    have hc := congrArg (mapMu6 (invMatch σ)) heq
    rwa [mapMu6_left_inv hp (List.mem_permutations.1 h1),
      mapMu6_left_inv hp (List.mem_permutations.1 h2)] at hc
  rw [List.perm_ext_iff_of_nodup hndm hnd]
  intro mu'
  constructor
  · intro hmem
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hmem
    exact mapMu6_mem_perms hp hmu
  · intro hmem
    refine List.mem_map.2 ⟨mapMu6 (invMatch σ) mu', ?_, ?_⟩
    · exact mapMu6_mem_perms (invMatch_perm hp) hmem
    · have hp' := List.mem_permutations.1 hmem
      have := mapMu6_left_inv (invMatch_perm hp)
        (List.mem_permutations.1 hmem)
      rwa [invMatch_invMatch hp] at this

/-- **Relabeling invariance of the stable-matching count** —
the instance-level content of Lemma sym (ii). -/
theorem stableCount6_relabel6 {σ : List Nat} (hp : σ.Perm idRow6)
    (I : Inst6) :
    stableCount6 (relabel6 σ I) = stableCount6 I := by
  unfold stableCount6 sms6
  have hperm := perms_mapMu6_perm (σ := σ) hp
  have h1 := (hperm.filter (isStable6 (relabel6 σ I))).length_eq
  rw [← h1, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro mu hmu
  show isStable6 (relabel6 σ I) (mapMu6 σ mu) = isStable6 I mu
  exact isStable6_relabel6 hp (List.mem_permutations.1 hmu)
