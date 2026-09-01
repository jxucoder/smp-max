import SmpF5.SixBridge

/-!
# The stable-matching lattice, order 6: the meet lemma

`meetM I μ ν` gives every man the better (by his ranking in `I`) of his
partners in the stable matchings `μ` and `ν`. The classical lattice
lemma: `meetM` is again a stable matching. This is the cornerstone of
the coverage argument for f(6).
-/

def meetM (I : Inst6) (μ ν : List Nat) : List Nat :=
  (List.range 6).map fun m =>
    if get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m (ν.getD m 0)
    then μ.getD m 0 else ν.getD m 0

/-! ## Helpers -/

theorem partner_idxOf {mu : List Nat} (hp : mu.Perm idRow6) {a : Nat}
    (ha : a < 6) : idxOf (mu.getD a 0) mu = a := by
  have hnd : mu.Nodup := hp.nodup_iff.2 (by decide)
  exact idxOf_getD hnd (by rw [perm6_length hp]; exact ha)

theorem partner_idxOf_of_eq {mu : List Nat} (hp : mu.Perm idRow6) {b w : Nat}
    (hb : b < 6) (heq : mu.getD b 0 = w) : idxOf w mu = b := by
  rw [← heq]
  exact partner_idxOf hp hb

/-- Stability instance extraction: no blocking pair. -/
theorem no_block {I : Inst6} {mu : List Nat} (h : mu ∈ sms6 I) {m w : Nat}
    (hm : m < 6) (hw : w < 6) (hne : w ≠ mu.getD m 0)
    (hpref : get2 I.mrank m w < get2 I.mrank m (mu.getD m 0)) :
    ¬ (get2 I.wrank w m < get2 I.wrank w (idxOf w mu)) := by
  have hst := mem_sms6_stable h
  simp only [isStable6, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not] at hst
  rcases hst m hm w hw with h1 | h2 | h2
  · exact absurd h1 hne
  · exact absurd hpref h2
  · exact h2

theorem meet_getD {I : Inst6} {μ ν : List Nat} {m : Nat} (hm : m < 6) :
    (meetM I μ ν).getD m 0 =
      if get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m (ν.getD m 0)
      then μ.getD m 0 else ν.getD m 0 := by
  simp only [meetM]
  rw [getD_map_range6 hm]

theorem meet_eq_or {I : Inst6} {μ ν : List Nat} {m : Nat} (hm : m < 6) :
    (meetM I μ ν).getD m 0 = μ.getD m 0 ∨
    (meetM I μ ν).getD m 0 = ν.getD m 0 := by
  rw [meet_getD hm]
  split <;> simp

theorem meet_best {I : Inst6} {μ ν : List Nat} {m : Nat} (hm : m < 6) :
    get2 I.mrank m ((meetM I μ ν).getD m 0) ≤ get2 I.mrank m (μ.getD m 0) ∧
    get2 I.mrank m ((meetM I μ ν).getD m 0) ≤ get2 I.mrank m (ν.getD m 0) := by
  rw [meet_getD hm]
  split
  · next hc => exact ⟨le_refl _, hc⟩
  · next hc => exact ⟨by omega, le_refl _⟩

/-! ## The core blocking contradiction -/

/-- If `w = σ(a) = τ(b)` for stable `σ, τ` with `a ≠ b`, and `a` strictly
prefers `w` to his `τ`-partner while `b` strictly prefers `w` to his
`σ`-partner, then `w` must prefer each of them over the other:
contradiction. -/
theorem meet_inj_core {I : Inst6}
    (hwl : I.wrank.length = 6)
    (hwrows : ∀ r ∈ I.wrank, isRankRow6 r = true)
    {σ τ : List Nat} (hσ : σ ∈ sms6 I) (hτ : τ ∈ sms6 I)
    {a b w : Nat} (ha : a < 6) (hb : b < 6) (hw6 : w < 6) (hab : a ≠ b)
    (hwa : σ.getD a 0 = w) (hwb : τ.getD b 0 = w)
    (hsa : get2 I.mrank a w < get2 I.mrank a (τ.getD a 0))
    (hsb : get2 I.mrank b w < get2 I.mrank b (σ.getD b 0)) : False := by
  have hpσ := mem_sms6_perm hσ
  have hpτ := mem_sms6_perm hτ
  have hne_a : w ≠ τ.getD a 0 := by
    intro hc; rw [← hc] at hsa; omega
  have hne_b : w ≠ σ.getD b 0 := by
    intro hc; rw [← hc] at hsb; omega
  have h1 := no_block hτ ha hw6 hne_a hsa
  rw [partner_idxOf_of_eq hpτ hb hwb] at h1
  have h2 := no_block hσ hb hw6 hne_b hsb
  rw [partner_idxOf_of_eq hpσ ha hwa] at h2
  have hne : get2 I.wrank w a ≠ get2 I.wrank w b :=
    fun hc => hab (rank_inj6 hwl hwrows hw6 ha hb hc)
  omega

/-! ## Injectivity of the meet -/

theorem meet_inj {I : Inst6} (hWF : WF6 I = true) {μ ν : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) {a b : Nat}
    (ha : a < 6) (hb : b < 6) (hab : a ≠ b)
    (heq : (meetM I μ ν).getD a 0 = (meetM I μ ν).getD b 0) : False := by
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hWF
  obtain ⟨⟨⟨hml, hwl⟩, hmrows⟩, hwrows⟩ := hWF
  have hpμ := mem_sms6_perm hμ
  have hpν := mem_sms6_perm hν
  obtain ⟨w, hwdef⟩ : ∃ w, (meetM I μ ν).getD a 0 = w := ⟨_, rfl⟩
  have hw6 : w < 6 := by
    rcases meet_eq_or (I := I) (μ := μ) (ν := ν) ha with h | h
    · rw [← hwdef, h]; exact perm6_getD_lt hpμ ha
    · rw [← hwdef, h]; exact perm6_getD_lt hpν ha
  rcases meet_eq_or (I := I) (μ := μ) (ν := ν) ha with haμ | haν
  · rcases meet_eq_or (I := I) (μ := μ) (ν := ν) hb with hbμ | hbν
    · -- both from μ
      apply hab
      have h1 : μ.getD a 0 = μ.getD b 0 := by rw [← haμ, heq, hbμ]
      calc a = idxOf (μ.getD a 0) μ := (partner_idxOf hpμ ha).symm
        _ = idxOf (μ.getD b 0) μ := by rw [h1]
        _ = b := partner_idxOf hpμ hb
    · -- a from μ, b from ν: w = μ(a) = ν(b); core with σ := μ, τ := ν
      have hwa : μ.getD a 0 = w := by rw [← haμ, hwdef]
      have hwb : ν.getD b 0 = w := by rw [← hbν, ← heq, hwdef]
      have hνa_ne : ν.getD a 0 ≠ w := fun hc => hab
        (by calc a = idxOf (ν.getD a 0) ν := (partner_idxOf hpν ha).symm
              _ = idxOf (ν.getD b 0) ν := by rw [hc, hwb]
              _ = b := partner_idxOf hpν hb)
      have hμb_ne : μ.getD b 0 ≠ w := fun hc => hab
        (by calc a = idxOf (μ.getD a 0) μ := (partner_idxOf hpμ ha).symm
              _ = idxOf (μ.getD b 0) μ := by rw [hwa, hc]
              _ = b := partner_idxOf hpμ hb)
      have hsa : get2 I.mrank a w < get2 I.mrank a (ν.getD a 0) := by
        have hle := (meet_best (I := I) (μ := μ) (ν := ν) ha).2
        rw [hwdef] at hle
        have hne : get2 I.mrank a w ≠ get2 I.mrank a (ν.getD a 0) :=
          fun hc => hνa_ne ((rank_inj6 hml hmrows ha hw6
            (perm6_getD_lt hpν ha) hc).symm)
        omega
      have hsb : get2 I.mrank b w < get2 I.mrank b (μ.getD b 0) := by
        have hgd := meet_getD (I := I) (μ := μ) (ν := ν) hb
        rw [← heq, hwdef] at hgd
        by_cases hc : get2 I.mrank b (μ.getD b 0) ≤ get2 I.mrank b (ν.getD b 0)
        · rw [if_pos hc] at hgd
          exact absurd hgd.symm hμb_ne
        · rw [if_neg hc] at hgd
          rw [← hgd] at hc
          omega
      exact meet_inj_core hwl hwrows hμ hν ha hb hw6 hab hwa hwb hsa hsb
  · rcases meet_eq_or (I := I) (μ := μ) (ν := ν) hb with hbμ | hbν
    · -- a from ν, b from μ: w = ν(a) = μ(b); core with σ := ν, τ := μ
      have hwa : ν.getD a 0 = w := by rw [← haν, hwdef]
      have hwb : μ.getD b 0 = w := by rw [← hbμ, ← heq, hwdef]
      have hμa_ne : μ.getD a 0 ≠ w := fun hc => hab
        (by calc a = idxOf (μ.getD a 0) μ := (partner_idxOf hpμ ha).symm
              _ = idxOf (μ.getD b 0) μ := by rw [hc, hwb]
              _ = b := partner_idxOf hpμ hb)
      have hνb_ne : ν.getD b 0 ≠ w := fun hc => hab
        (by calc a = idxOf (ν.getD a 0) ν := (partner_idxOf hpν ha).symm
              _ = idxOf (ν.getD b 0) ν := by rw [hwa, hc]
              _ = b := partner_idxOf hpν hb)
      have hsa : get2 I.mrank a w < get2 I.mrank a (μ.getD a 0) := by
        have hgd := meet_getD (I := I) (μ := μ) (ν := ν) ha
        rw [hwdef] at hgd
        by_cases hc : get2 I.mrank a (μ.getD a 0) ≤ get2 I.mrank a (ν.getD a 0)
        · rw [if_pos hc] at hgd
          exact absurd hgd.symm hμa_ne
        · rw [if_neg hc] at hgd
          rw [← hgd] at hc
          omega
      have hsb : get2 I.mrank b w < get2 I.mrank b (ν.getD b 0) := by
        have hle := (meet_best (I := I) (μ := μ) (ν := ν) hb).2
        rw [← heq, hwdef] at hle
        have hne : get2 I.mrank b w ≠ get2 I.mrank b (ν.getD b 0) :=
          fun hc => hνb_ne ((rank_inj6 hml hmrows hb hw6
            (perm6_getD_lt hpν hb) hc).symm)
        omega
      exact meet_inj_core hwl hwrows hν hμ ha hb hw6 hab hwa hwb hsa hsb
    · -- both from ν
      apply hab
      have h1 : ν.getD a 0 = ν.getD b 0 := by rw [← haν, heq, hbν]
      calc a = idxOf (ν.getD a 0) ν := (partner_idxOf hpν ha).symm
        _ = idxOf (ν.getD b 0) ν := by rw [h1]
        _ = b := partner_idxOf hpν hb

/-! ## The meet is a stable matching -/

theorem meet_perm {I : Inst6} (hWF : WF6 I = true) {μ ν : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) :
    (meetM I μ ν).Perm idRow6 := by
  have hpμ := mem_sms6_perm hμ
  have hpν := mem_sms6_perm hν
  have hlen : (meetM I μ ν).length = 6 := by simp [meetM]
  have hnd : (meetM I μ ν).Nodup := by
    unfold meetM
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha' b hb' heq'
    by_contra hab
    have ha : a < 6 := by simpa using ha'
    have hb : b < 6 := by simpa using hb'
    refine meet_inj hWF hμ hν ha hb hab ?_
    rw [meet_getD ha, meet_getD hb]
    exact heq'
  have hsub : meetM I μ ν ⊆ idRow6 := by
    intro x hx
    unfold meetM at hx
    obtain ⟨m, hm', hxeq⟩ := List.mem_map.1 hx
    have hm : m < 6 := by simpa using hm'
    have hx6 : x < 6 := by
      rw [← hxeq]
      split
      · exact perm6_getD_lt hpμ hm
      · exact perm6_getD_lt hpν hm
    simp only [idRow6, List.mem_cons]
    omega
  have hsp : (meetM I μ ν).Subperm idRow6 := hnd.subperm hsub
  exact hsp.perm_of_length_le (by simp [hlen, idRow6])

theorem meet_stable {I : Inst6} (hWF : WF6 I = true) {μ ν : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) :
    isStable6 I (meetM I μ ν) = true := by
  have hpμ := mem_sms6_perm hμ
  have hpν := mem_sms6_perm hν
  have hpm := meet_perm hWF hμ hν
  simp only [isStable6, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  intro m hm w hw
  by_cases heq : w = (meetM I μ ν).getD m 0
  · exact Or.inl heq
  · right
    by_cases hA : get2 I.mrank m w < get2 I.mrank m ((meetM I μ ν).getD m 0)
    · right
      intro hB
      -- m strictly prefers w to both his μ- and ν-partners
      have hbest := meet_best (I := I) (μ := μ) (ν := ν) hm
      have hAμ : get2 I.mrank m w < get2 I.mrank m (μ.getD m 0) := by omega
      have hAν : get2 I.mrank m w < get2 I.mrank m (ν.getD m 0) := by omega
      have hneμ : w ≠ μ.getD m 0 := by
        intro hc; rw [← hc] at hAμ; omega
      have hneν : w ≠ ν.getD m 0 := by
        intro hc; rw [← hc] at hAν; omega
      -- w's meet-partner came from μ or ν
      have hwmem : w ∈ meetM I μ ν := perm6_mem hpm hw
      have hm'6 : idxOf w (meetM I μ ν) < 6 := by
        have := idxOf_lt_length hwmem
        rw [perm6_length hpm] at this
        exact this
      have hgot : (meetM I μ ν).getD (idxOf w (meetM I μ ν)) 0 = w :=
        getD_idxOf hwmem
      rcases meet_eq_or (I := I) (μ := μ) (ν := ν) hm'6 with hσ | hσ
      · -- from μ: w's μ-partner is the meet partner
        have hidx : idxOf w μ = idxOf w (meetM I μ ν) :=
          partner_idxOf_of_eq hpμ hm'6 (by rw [← hσ, hgot])
        exact no_block hμ hm hw hneμ hAμ (by rw [hidx]; exact hB)
      · have hidx : idxOf w ν = idxOf w (meetM I μ ν) :=
          partner_idxOf_of_eq hpν hm'6 (by rw [← hσ, hgot])
        exact no_block hν hm hw hneν hAν (by rw [hidx]; exact hB)
    · exact Or.inl hA

theorem meet_mem {I : Inst6} (hWF : WF6 I = true) {μ ν : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) :
    meetM I μ ν ∈ sms6 I :=
  List.mem_filter.2 ⟨List.mem_permutations.2 (meet_perm hWF hμ hν),
    meet_stable hWF hμ hν⟩

/-! ## Opposite interests -/

theorem idxOf_lt6 {mu : List Nat} (hp : mu.Perm idRow6) {w : Nat}
    (hw : w < 6) : idxOf w mu < 6 := by
  have := idxOf_lt_length (perm6_mem hp hw)
  rw [perm6_length hp] at this
  exact this

/-- If every man weakly prefers `μ` to `ν`, then every woman weakly
prefers `ν` to `μ`. -/
theorem opposite_interests {I : Inst6} (hWF : WF6 I = true)
    {μ ν : List Nat} (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I)
    (hdom : ∀ m, m < 6 →
      get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m (ν.getD m 0))
    {w : Nat} (hw : w < 6) :
    get2 I.wrank w (idxOf w ν) ≤ get2 I.wrank w (idxOf w μ) := by
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hWF
  obtain ⟨⟨⟨hml, hwl⟩, hmrows⟩, hwrows⟩ := hWF
  have hpμ := mem_sms6_perm hμ
  have hpν := mem_sms6_perm hν
  have ha6 : idxOf w μ < 6 := idxOf_lt6 hpμ hw
  have hb6 : idxOf w ν < 6 := idxOf_lt6 hpν hw
  by_cases hab : idxOf w μ = idxOf w ν
  · rw [hab]
  · by_contra hcon
    -- w strictly prefers her μ-husband a to her ν-husband b
    have hstrict_w : get2 I.wrank w (idxOf w μ) < get2 I.wrank w (idxOf w ν) := by
      have hne : get2 I.wrank w (idxOf w μ) ≠ get2 I.wrank w (idxOf w ν) :=
        fun hc => hab (rank_inj6 hwl hwrows hw ha6 hb6 hc)
      omega
    have hμa : μ.getD (idxOf w μ) 0 = w := getD_idxOf (perm6_mem hpμ hw)
    -- a's ν-partner is not w
    have hνa_ne : ν.getD (idxOf w μ) 0 ≠ w := by
      intro hc
      exact hab (partner_idxOf_of_eq hpν ha6 hc).symm
    -- a strictly prefers w to his ν-partner
    have hpref : get2 I.mrank (idxOf w μ) w <
        get2 I.mrank (idxOf w μ) (ν.getD (idxOf w μ) 0) := by
      have hd := hdom (idxOf w μ) ha6
      rw [hμa] at hd
      have hne : get2 I.mrank (idxOf w μ) w ≠
          get2 I.mrank (idxOf w μ) (ν.getD (idxOf w μ) 0) :=
        fun hc => hνa_ne ((rank_inj6 hml hmrows ha6 hw
          (perm6_getD_lt hpν ha6) hc).symm)
      omega
    exact no_block hν ha6 hw (fun hc => hνa_ne hc.symm) hpref hstrict_w

/-! ## Transpose duality and the join -/

def transposeI (I : Inst6) : Inst6 := ⟨I.wrank, I.mrank⟩

def invMatch (mu : List Nat) : List Nat :=
  (List.range 6).map fun w => idxOf w mu

theorem invMatch_getD {mu : List Nat} {w : Nat} (hw : w < 6) :
    (invMatch mu).getD w 0 = idxOf w mu := by
  unfold invMatch
  exact getD_map_range6 hw

theorem partner_eq_iff {mu : List Nat} (hp : mu.Perm idRow6) {m w : Nat}
    (hm : m < 6) (hw : w < 6) :
    mu.getD m 0 = w ↔ idxOf w mu = m := by
  constructor
  · exact partner_idxOf_of_eq hp hm
  · intro h
    rw [← h]
    exact getD_idxOf (perm6_mem hp hw)

theorem invMatch_perm {mu : List Nat} (hp : mu.Perm idRow6) :
    (invMatch mu).Perm idRow6 := by
  have hlen : (invMatch mu).length = 6 := by simp [invMatch]
  have hnd : (invMatch mu).Nodup := by
    unfold invMatch
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha' b hb' heq'
    have ha : a < 6 := by simpa using ha'
    have hb : b < 6 := by simpa using hb'
    have h1 : mu.getD (idxOf a mu) 0 = a := getD_idxOf (perm6_mem hp ha)
    have h2 : mu.getD (idxOf b mu) 0 = b := getD_idxOf (perm6_mem hp hb)
    rw [heq', h2] at h1
    exact h1.symm
  have hsub : invMatch mu ⊆ idRow6 := by
    intro x hx
    obtain ⟨w, hw', hxeq⟩ := List.mem_map.1 hx
    have hw : w < 6 := by simpa using hw'
    have : x < 6 := by rw [← hxeq]; exact idxOf_lt6 hp hw
    simp only [idRow6, List.mem_cons]
    omega
  exact (hnd.subperm hsub).perm_of_length_le (by simp [hlen, idRow6])

theorem idxOf_invMatch {mu : List Nat} (hp : mu.Perm idRow6) {m : Nat}
    (hm : m < 6) : idxOf m (invMatch mu) = mu.getD m 0 := by
  have hpi := invMatch_perm hp
  have hw6 : mu.getD m 0 < 6 := perm6_getD_lt hp hm
  refine partner_idxOf_of_eq hpi hw6 ?_
  rw [invMatch_getD hw6]
  exact partner_idxOf hp hm

theorem invMatch_invMatch {mu : List Nat} (hp : mu.Perm idRow6) :
    invMatch (invMatch mu) = mu := by
  apply List.ext_getElem
  · rw [perm6_length (invMatch_perm (invMatch_perm hp)), perm6_length hp]
  · intro i h1 h2
    have hi : i < 6 := by
      rw [perm6_length hp] at h2
      exact h2
    rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2,
        invMatch_getD hi, idxOf_invMatch hp hi]

theorem WF6_transposeI {I : Inst6} (h : WF6 I = true) :
    WF6 (transposeI I) = true := by
  simp only [WF6, transposeI, Bool.and_eq_true] at h ⊢
  exact ⟨⟨⟨h.1.1.2, h.1.1.1⟩, h.2⟩, h.1.2⟩

/-- Stability is self-dual under transposition. -/
theorem isStable6_transposeI {I : Inst6} {mu : List Nat}
    (hp : mu.Perm idRow6) :
    isStable6 (transposeI I) (invMatch mu) = isStable6 I mu := by
  have hm1 : (transposeI I).mrank = I.wrank := rfl
  have hm2 : (transposeI I).wrank = I.mrank := rfl
  rw [Bool.eq_iff_iff]
  simp only [isStable6, hm1, hm2, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · intro H m hm w hw
    have := H w hw m hm
    rw [invMatch_getD hw, idxOf_invMatch hp hm] at this
    rcases this with h1 | h2 | h2
    · left
      exact ((partner_eq_iff hp hm hw).2 h1.symm).symm
    · right; right; omega
    · right; left; omega
  · intro H w hw m hm
    have := H m hm w hw
    rw [invMatch_getD hw, idxOf_invMatch hp hm]
    rcases this with h1 | h2 | h2
    · left
      exact ((partner_eq_iff hp hm hw).1 h1.symm).symm
    · right; right; omega
    · right; left; omega

theorem mem_sms6_transposeI {I : Inst6} {mu : List Nat}
    (hmu : mu ∈ sms6 I) : invMatch mu ∈ sms6 (transposeI I) := by
  have hp := mem_sms6_perm hmu
  refine List.mem_filter.2 ⟨List.mem_permutations.2 (invMatch_perm hp), ?_⟩
  rw [isStable6_transposeI hp]
  exact mem_sms6_stable hmu

def joinS (I : Inst6) (μ ν : List Nat) : List Nat :=
  invMatch (meetM (transposeI I) (invMatch μ) (invMatch ν))

theorem join_mem {I : Inst6} (hWF : WF6 I = true) {μ ν : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) :
    joinS I μ ν ∈ sms6 I := by
  have hWFt := WF6_transposeI hWF
  have hρ : meetM (transposeI I) (invMatch μ) (invMatch ν) ∈
      sms6 (transposeI I) :=
    meet_mem hWFt (mem_sms6_transposeI hμ) (mem_sms6_transposeI hν)
  have hpρ := mem_sms6_perm hρ
  refine List.mem_filter.2
    ⟨List.mem_permutations.2 (invMatch_perm hpρ), ?_⟩
  show isStable6 I (invMatch (meetM (transposeI I) (invMatch μ) (invMatch ν))) = true
  have hdual := isStable6_transposeI (I := transposeI I) hpρ
  rw [show transposeI (transposeI I) = I from rfl] at hdual
  rw [hdual]
  exact mem_sms6_stable hρ

/-! ## The man-optimal matching (L3) -/

def manOpt (I : Inst6) : List Nat :=
  match sms6 I with
  | [] => idRow6
  | mu :: rest => rest.foldl (meetM I) mu

theorem foldl_meet_spec {I : Inst6} (hWF : WF6 I = true) :
    ∀ (L : List (List Nat)) (acc : List Nat), acc ∈ sms6 I →
    (∀ x ∈ L, x ∈ sms6 I) →
    (L.foldl (meetM I) acc ∈ sms6 I) ∧
    (∀ m, m < 6 → get2 I.mrank m ((L.foldl (meetM I) acc).getD m 0) ≤
      get2 I.mrank m (acc.getD m 0)) ∧
    (∀ x ∈ L, ∀ m, m < 6 → get2 I.mrank m ((L.foldl (meetM I) acc).getD m 0) ≤
      get2 I.mrank m (x.getD m 0)) := by
  intro L
  induction L with
  | nil =>
    intro acc hacc _
    exact ⟨hacc, fun m hm => le_refl _, by simp⟩
  | cons x L ih =>
    intro acc hacc hL
    have hx : x ∈ sms6 I := hL x List.mem_cons_self
    have hacc' : meetM I acc x ∈ sms6 I := meet_mem hWF hacc hx
    obtain ⟨h1, h2, h3⟩ := ih (meetM I acc x) hacc'
      (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    simp only [List.foldl_cons]
    refine ⟨h1, ?_, ?_⟩
    · intro m hm
      have hb := (meet_best (I := I) (μ := acc) (ν := x) hm).1
      have h2m := h2 m hm
      omega
    · intro y hy m hm
      rcases List.mem_cons.1 hy with rfl | hy'
      · have hb := (meet_best (I := I) (μ := acc) (ν := y) hm).2
        have h2m := h2 m hm
        omega
      · exact h3 y hy' m hm

theorem manOpt_spec {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ []) :
    manOpt I ∈ sms6 I ∧
    ∀ ν ∈ sms6 I, ∀ m, m < 6 →
      get2 I.mrank m ((manOpt I).getD m 0) ≤ get2 I.mrank m (ν.getD m 0) := by
  rcases hsms : sms6 I with _ | ⟨mu, rest⟩
  · exact absurd hsms hne
  · have hmu : mu ∈ sms6 I := by rw [hsms]; exact List.mem_cons_self
    have hrest : ∀ x ∈ rest, x ∈ sms6 I := by
      intro x hx; rw [hsms]; exact List.mem_cons_of_mem _ hx
    obtain ⟨h1, h2, h3⟩ := foldl_meet_spec hWF rest mu hmu hrest
    have hman : manOpt I = rest.foldl (meetM I) mu := by
      simp only [manOpt, hsms]
    constructor
    · rw [hman, ← hsms]; exact h1
    · intro ν hν m hm
      rw [hman]
      rcases List.mem_cons.1 hν with rfl | hν'
      · exact h2 m hm
      · exact h3 ν hν' m hm

/-- Dominance is antisymmetric on stable matchings. -/
theorem dominance_antisymm {I : Inst6} (hWF : WF6 I = true)
    {μ ν : List Nat} (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I)
    (h1 : ∀ m, m < 6 →
      get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m (ν.getD m 0))
    (h2 : ∀ m, m < 6 →
      get2 I.mrank m (ν.getD m 0) ≤ get2 I.mrank m (μ.getD m 0)) :
    μ = ν := by
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hWF
  obtain ⟨⟨⟨hml, _⟩, hmrows⟩, _⟩ := hWF
  have hpμ := mem_sms6_perm hμ
  have hpν := mem_sms6_perm hν
  apply List.ext_getElem
  · rw [perm6_length hpμ, perm6_length hpν]
  · intro i hi1 hi2
    have hi : i < 6 := by rw [perm6_length hpμ] at hi1; exact hi1
    rw [← List.getD_eq_getElem _ _ hi1, ← List.getD_eq_getElem _ _ hi2]
    exact rank_inj6 hml hmrows hi (perm6_getD_lt hpμ hi)
      (perm6_getD_lt hpν hi) (by have := h1 i hi; have := h2 i hi; omega)

/-! ## Pointwise characterization of the join (L4 prep) -/

theorem joinS_eq_or {I : Inst6} (hWF : WF6 I = true) {μ ν : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) {m : Nat} (hm : m < 6) :
    (joinS I μ ν).getD m 0 = μ.getD m 0 ∨
    (joinS I μ ν).getD m 0 = ν.getD m 0 := by
  have hpμ := mem_sms6_perm hμ
  have hpν := mem_sms6_perm hν
  have hρ : meetM (transposeI I) (invMatch μ) (invMatch ν) ∈
      sms6 (transposeI I) :=
    meet_mem (WF6_transposeI hWF) (mem_sms6_transposeI hμ)
      (mem_sms6_transposeI hν)
  have hpρ := mem_sms6_perm hρ
  have hj : (joinS I μ ν).getD m 0 =
      idxOf m (meetM (transposeI I) (invMatch μ) (invMatch ν)) := by
    change (invMatch _).getD m 0 = _
    exact invMatch_getD hm
  have hw6 : (joinS I μ ν).getD m 0 < 6 := by
    rw [hj]
    exact idxOf_lt6 hpρ hm
  have hlw : (meetM (transposeI I) (invMatch μ) (invMatch ν)).getD
      ((joinS I μ ν).getD m 0) 0 = m := by
    rw [hj]
    exact getD_idxOf (perm6_mem hpρ hm)
  rcases meet_eq_or (I := transposeI I) (μ := invMatch μ) (ν := invMatch ν)
    (m := (joinS I μ ν).getD m 0) hw6 with h | h
  · left
    rw [hlw, invMatch_getD hw6] at h
    exact ((partner_eq_iff hpμ hm hw6).2 h.symm).symm
  · right
    rw [hlw, invMatch_getD hw6] at h
    exact ((partner_eq_iff hpν hm hw6).2 h.symm).symm

theorem joinS_ge {I : Inst6} (hWF : WF6 I = true) {μ ν : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) {m : Nat} (hm : m < 6) :
    get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m ((joinS I μ ν).getD m 0) ∧
    get2 I.mrank m (ν.getD m 0) ≤ get2 I.mrank m ((joinS I μ ν).getD m 0) := by
  have hWFt := WF6_transposeI hWF
  have hρ : meetM (transposeI I) (invMatch μ) (invMatch ν) ∈
      sms6 (transposeI I) :=
    meet_mem hWFt (mem_sms6_transposeI hμ) (mem_sms6_transposeI hν)
  have hj : ∀ x, x < 6 → (joinS I μ ν).getD x 0 =
      idxOf x (meetM (transposeI I) (invMatch μ) (invMatch ν)) := by
    intro x hx
    change (invMatch _).getD x 0 = _
    exact invMatch_getD hx
  constructor
  · -- opposite interests in the transposed world, λ vs invMatch μ
    have hdom : ∀ w, w < 6 →
        get2 (transposeI I).mrank w
          ((meetM (transposeI I) (invMatch μ) (invMatch ν)).getD w 0) ≤
        get2 (transposeI I).mrank w ((invMatch μ).getD w 0) :=
      fun w hw => (meet_best (I := transposeI I) (μ := invMatch μ)
        (ν := invMatch ν) hw).1
    have hoi := opposite_interests hWFt hρ (mem_sms6_transposeI hμ) hdom
      (w := m) hm
    rw [show (transposeI I).wrank = I.mrank from rfl] at hoi
    rw [idxOf_invMatch (mem_sms6_perm hμ) hm, ← hj m hm] at hoi
    exact hoi
  · have hdom : ∀ w, w < 6 →
        get2 (transposeI I).mrank w
          ((meetM (transposeI I) (invMatch μ) (invMatch ν)).getD w 0) ≤
        get2 (transposeI I).mrank w ((invMatch ν).getD w 0) :=
      fun w hw => (meet_best (I := transposeI I) (μ := invMatch μ)
        (ν := invMatch ν) hw).2
    have hoi := opposite_interests hWFt hρ (mem_sms6_transposeI hν) hdom
      (w := m) hm
    rw [show (transposeI I).wrank = I.mrank from rfl] at hoi
    rw [idxOf_invMatch (mem_sms6_perm hν) hm, ← hj m hm] at hoi
    exact hoi

/-! ## The no-skip lemma (L4) -/

def domLe (I : Inst6) (μ ν : List Nat) : Prop :=
  ∀ m, m < 6 → get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m (ν.getD m 0)

/-- On a cover `μ ⋖ ν` of the dominance order, no man passes over a
stable partner: there is no stable `σ` with
`rank(μ(m)) < rank(σ(m)) < rank(ν(m))`. -/
theorem no_skip {I : Inst6} (hWF : WF6 I = true) {μ ν σ : List Nat}
    (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I) (hσ : σ ∈ sms6 I)
    (hdom : domLe I μ ν)
    (hcov : ∀ τ ∈ sms6 I, domLe I μ τ → domLe I τ ν → τ = μ ∨ τ = ν)
    {m : Nat} (hm : m < 6) :
    ¬(get2 I.mrank m (μ.getD m 0) < get2 I.mrank m (σ.getD m 0) ∧
      get2 I.mrank m (σ.getD m 0) < get2 I.mrank m (ν.getD m 0)) := by
  rintro ⟨hs1, hs2⟩
  have hjmem := join_mem hWF hμ hσ
  have hτmem := meet_mem hWF hν hjmem
  have hjm : (joinS I μ σ).getD m 0 = σ.getD m 0 := by
    rcases joinS_eq_or hWF hμ hσ hm with h | h
    · exfalso
      have hge := (joinS_ge hWF hμ hσ hm).2
      rw [h] at hge
      omega
    · exact h
  have hτm : (meetM I ν (joinS I μ σ)).getD m 0 = σ.getD m 0 := by
    rw [meet_getD hm, hjm]
    rw [if_neg (by omega)]
  have hμτ : domLe I μ (meetM I ν (joinS I μ σ)) := by
    intro x hx
    rcases meet_eq_or (I := I) (μ := ν) (ν := joinS I μ σ) hx with h | h
    · rw [h]; exact hdom x hx
    · rw [h]; exact (joinS_ge hWF hμ hσ hx).1
  have hτν : domLe I (meetM I ν (joinS I μ σ)) ν := fun x hx =>
    (meet_best (I := I) (μ := ν) (ν := joinS I μ σ) hx).1
  rcases hcov _ hτmem hμτ hτν with h | h
  · rw [h] at hτm
    rw [hτm] at hs1
    omega
  · rw [h] at hτm
    rw [hτm] at hs2
    omega
