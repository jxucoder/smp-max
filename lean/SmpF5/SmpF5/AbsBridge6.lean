import SmpF5.Sched6

/-!
# The bottom-agnostic bridge

`bridge_stable` (SixBridge) is proved for the specific `promoteRank`
read-off. The blocking-pair argument never looks at how non-stable
partners are ordered, so it holds for *any* instance `J` that

* ranks each person's stable partners strictly monotonically in the
  original order, and
* ranks every stable partner above every non-stable one.

This abstract form serves both the promoted `readoff I` (re-derived
below as a cross-check) and the schedule read-off `readoffS`, whose
canonical bottom completion is not relabel-equivariant.
-/

theorem stable_of_orderPreserving {I J : Inst6} (h : WF6 I = true)
    (hm_mono : ∀ m, m < 6 → ∀ w, w < 6 → ∀ w', w' < 6 →
      stab I m w = true → stab I m w' = true →
      get2 I.mrank m w < get2 I.mrank m w' →
      get2 J.mrank m w < get2 J.mrank m w')
    (hm_top : ∀ m, m < 6 → ∀ w, w < 6 → ∀ w', w' < 6 →
      stab I m w = true → stab I m w' = false →
      get2 J.mrank m w < get2 J.mrank m w')
    (hw_mono : ∀ w, w < 6 → ∀ m, m < 6 → ∀ m', m' < 6 →
      stab I m w = true → stab I m' w = true →
      get2 I.wrank w m < get2 I.wrank w m' →
      get2 J.wrank w m < get2 J.wrank w m')
    {mu : List Nat} (hmu : mu ∈ sms6 I) : isStable6 J mu = true := by
  obtain ⟨hml, hmrows⟩ := mrank_facts h
  obtain ⟨hwl, hwrows⟩ := wrank_facts h
  have hp := mem_sms6_perm hmu
  have hst := mem_sms6_stable hmu
  simp only [isStable6, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not] at hst ⊢
  intro m hm w hw
  by_cases heq : w = mu.getD m 0
  · exact Or.inl heq
  · right
    have hwm6 : mu.getD m 0 < 6 := perm6_getD_lt hp hm
    have hmw6 : idxOf w mu < 6 := by
      have hwmem : w ∈ mu := perm6_mem hp hw
      have := idxOf_lt_length hwmem
      rw [perm6_length hp] at this
      exact this
    have hstwm : stab I m (mu.getD m 0) = true := stab_of_mem hmu
    have hstmw : stab I (idxOf w mu) w = true := stab_of_mem_w hmu hw
    have hmne : m ≠ idxOf w mu := by
      intro he
      apply heq
      have hwmem : w ∈ mu := perm6_mem hp hw
      rw [he]
      exact (getD_idxOf hwmem).symm
    by_cases hsw : stab I m w
    · have hbody := hst m hm w hw
      rcases hbody with h1 | h2 | h2
      · exact absurd h1 heq
      · left
        intro hcon
        have hne : get2 I.mrank m w ≠ get2 I.mrank m (mu.getD m 0) :=
          fun hc => heq (rank_inj6 hml hmrows hm hw hwm6 hc)
        have hlt' : get2 I.mrank m (mu.getD m 0) < get2 I.mrank m w := by
          omega
        have := hm_mono m hm (mu.getD m 0) hwm6 w hw hstwm hsw hlt'
        omega
      · right
        intro hcon
        have hne : get2 I.wrank w m ≠ get2 I.wrank w (idxOf w mu) :=
          fun hc => hmne (rank_inj6 hwl hwrows hw hm hmw6 hc)
        have hlt' : get2 I.wrank w (idxOf w mu) < get2 I.wrank w m := by
          omega
        have := hw_mono w hw (idxOf w mu) hmw6 m hm hstmw hsw hlt'
        omega
    · left
      intro hcon
      have hsw' : stab I m w = false := by simpa using hsw
      have := hm_top m hm (mu.getD m 0) hwm6 w hw hstwm hsw'
      omega

/-- Cross-check: the original promoted read-off satisfies the abstract
hypotheses, re-deriving `bridge_stable`. -/
theorem bridge_stable' {I : Inst6} (h : WF6 I = true) {mu : List Nat}
    (hmu : mu ∈ sms6 I) : isStable6 (readoff I) mu = true := by
  refine stable_of_orderPreserving h ?_ ?_ ?_ hmu
  · intro m hm w hw w' hw' hs hs' hlt
    rw [readoff_mrank hm hw, readoff_mrank hm hw']
    exact promoteRank_strict hs hs' hw (by simpa [get2] using hlt)
  · intro m hm w hw w' hw' hs hs'
    rw [readoff_mrank hm hw, readoff_mrank hm hw']
    exact promoteRank_promoted_lt hs hs' hw
  · intro w hw m hm m' hm' hs hs' hlt
    rw [readoff_wrank hw hm, readoff_wrank hw hm']
    exact promoteRank_strict (p := fun m'' => stab I m'' w)
      hs hs' hm (by simpa [get2] using hlt)

/-- Count-level corollary: any order-preserving `J` has at least as
many stable matchings as `I`. -/
theorem count_le_of_orderPreserving {I J : Inst6} (h : WF6 I = true)
    (hm_mono : ∀ m, m < 6 → ∀ w, w < 6 → ∀ w', w' < 6 →
      stab I m w = true → stab I m w' = true →
      get2 I.mrank m w < get2 I.mrank m w' →
      get2 J.mrank m w < get2 J.mrank m w')
    (hm_top : ∀ m, m < 6 → ∀ w, w < 6 → ∀ w', w' < 6 →
      stab I m w = true → stab I m w' = false →
      get2 J.mrank m w < get2 J.mrank m w')
    (hw_mono : ∀ w, w < 6 → ∀ m, m < 6 → ∀ m', m' < 6 →
      stab I m w = true → stab I m' w = true →
      get2 I.wrank w m < get2 I.wrank w m' →
      get2 J.wrank w m < get2 J.wrank w m') :
    stableCount6 I ≤ stableCount6 J := by
  unfold stableCount6 sms6
  refine (filter_sublist_of_imp ?_).length_le
  intro mu hmul hst
  exact stable_of_orderPreserving h hm_mono hm_top hw_mono
    (List.mem_filter.2 ⟨hmul, hst⟩)
