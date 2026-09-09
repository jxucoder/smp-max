import SmpMax.Six.ChainToSchedule

/-!
# Closing the Validity Lemma: sc(I) ≤ sc(readoffS (chainSched I))

The read-off instance of the chain schedule ranks each person's stable
partners on top in original preference order, so the bottom-agnostic
bridge (`count_le_of_orderPreserving`) applies.
-/

/-! ## Woman-side membership: `wtraj` = stable partners of `w` -/

theorem wtraj_subset_col {I : Inst6} {w m : Nat} (hm : m ∈ wtraj I w) :
    m ∈ (theChain I).map (fun mu => idxOf w mu) :=
  (List.destutter_sublist _ _).subset hm

theorem wtraj_mem_iff {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ [])
    {w : Nat} (hw : w < 6) {m : Nat} (hm : m < 6) :
    m ∈ wtraj I w ↔ stab I m w = true := by
  constructor
  · intro hmem
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.1 (wtraj_subset_col hmem)
    obtain ⟨hMmem, _⟩ := manOpt_spec hWF hne
    have hμmem : μ ∈ sms6 I := chainFrom_mem 31 (manOpt I) hMmem μ hμ
    have := stab_of_mem_sms6 hμmem (idxOf w μ)
    rwa [getD_idxOf (perm6_mem (mem_sms6_perm hμmem) hw)] at this
  · intro hst
    obtain ⟨x, hx, hxw⟩ := chain_complete hWF hm hst
    have hpx : x.Perm idRow6 := chain_mem_perm hWF hne hx
    have hidx : idxOf w x = m := partner_idxOf_of_eq hpx hm hxw
    refine mem_destutter_ne (List.mem_map.2 ⟨x, hx, hidx⟩)

/-! ## Generic `idxOf` position lemmas -/

theorem idxOf_append_mem {x : Nat} {A B : List Nat} (h : x ∈ A) :
    idxOf x (A ++ B) = idxOf x A := by
  induction A with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a t ih =>
    simp only [List.cons_append, idxOf]
    by_cases hax : a = x
    · rw [if_pos hax, if_pos hax]
    · rw [if_neg hax, if_neg hax]
      have hxt : x ∈ t := by
        rcases List.mem_cons.1 h with h1 | h1
        · exact absurd h1.symm hax
        · exact h1
      rw [ih hxt]

theorem idxOf_append_notMem {x : Nat} {A B : List Nat} (h : x ∉ A) :
    idxOf x (A ++ B) = A.length + idxOf x B := by
  induction A with
  | nil => simp
  | cons a t ih =>
    have hax : a ≠ x := fun he => h (he ▸ List.mem_cons_self)
    have hnt : x ∉ t := fun hc => h (List.mem_cons_of_mem _ hc)
    simp only [List.cons_append, idxOf, if_neg hax, List.length_cons]
    rw [ih hnt]; omega

theorem idxOf_lt_of_sorted {key : Nat → Nat} :
    ∀ (L : List Nat), L.Pairwise (fun a b => key a < key b) →
    ∀ {x y : Nat}, x ∈ L → y ∈ L → key x < key y → idxOf x L < idxOf y L := by
  intro L
  induction L with
  | nil => intro _ x y hx; exact absurd hx (List.not_mem_nil)
  | cons a t ih =>
    intro hpair x y hx hy hkey
    obtain ⟨hahead, htail⟩ := List.pairwise_cons.1 hpair
    simp only [idxOf]
    by_cases hax : a = x
    · rw [if_pos hax]
      by_cases hay : a = y
      · exact absurd (hax ▸ hay ▸ hkey) (lt_irrefl _)
      · rw [if_neg hay]; omega
    · rw [if_neg hax]
      have hxt : x ∈ t := by
        rcases List.mem_cons.1 hx with h1 | h1
        · exact absurd h1.symm hax
        · exact h1
      by_cases hay : a = y
      · exact absurd (hay ▸ hahead x hxt) (by omega)
      · rw [if_neg hay]
        have hyt : y ∈ t := by
          rcases List.mem_cons.1 hy with h1 | h1
          · exact absurd h1.symm hay
          · exact h1
        have := ih htail hxt hyt hkey
        omega

/-! ## Read-off ranks as positions -/

theorem get2_readoffS_mrank {S : List (List Nat)} {m w : Nat} (hm : m < 6)
    (hw : w < 6) :
    get2 (readoffS S).mrank m w = idxOf w (rowOrderM S m) := by
  show ((readoffS S).mrank.getD m []).getD w 0 = _
  unfold readoffS rankOfOrder
  rw [getD_map_range6 hm, getD_map_range6 hw]

theorem get2_readoffS_wrank {S : List (List Nat)} {w m : Nat} (hw : w < 6)
    (hm : m < 6) :
    get2 (readoffS S).wrank w m = idxOf m (rowOrderW S w) := by
  show ((readoffS S).wrank.getD w []).getD m 0 = _
  unfold readoffS rankOfOrder
  rw [getD_map_range6 hw, getD_map_range6 hm]

/-! ## The order-preserving properties at `readoffS (chainSched I)` -/

section
variable {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ [])
  (hmo : manOpt I = idRow6)

include hWF hne hmo in
/-- `w` is in the trajectory prefix of `rowOrderM` iff `w` is a stable
partner. -/
theorem mem_traj_prefix {m : Nat} (hm : m < 6) {w : Nat} (hw : w < 6) :
    (w ∈ strajM (chainSched I) m) ↔ stab I m w = true := by
  rw [strajM_eq_traj hWF hne hmo hm]
  exact traj_mem_iff hWF hne hm

include hWF hne hmo in
theorem readoffS_mrank_mono {m : Nat} (hm : m < 6) {w w' : Nat}
    (hw : w < 6) (hw' : w' < 6) (hsw : stab I m w = true)
    (hsw' : stab I m w' = true)
    (hlt : get2 I.mrank m w < get2 I.mrank m w') :
    get2 (readoffS (chainSched I)).mrank m w
      < get2 (readoffS (chainSched I)).mrank m w' := by
  rw [get2_readoffS_mrank hm hw, get2_readoffS_mrank hm hw']
  have hwmem : w ∈ strajM (chainSched I) m :=
    (mem_traj_prefix hWF hne hmo hm hw).2 hsw
  have hw'mem : w' ∈ strajM (chainSched I) m :=
    (mem_traj_prefix hWF hne hmo hm hw').2 hsw'
  unfold rowOrderM
  rw [idxOf_append_mem hwmem, idxOf_append_mem hw'mem]
  have hpair : (strajM (chainSched I) m).Pairwise
      (fun a b => get2 I.mrank m a < get2 I.mrank m b) := by
    rw [strajM_eq_traj hWF hne hmo hm]
    exact traj_rank_pairwise hWF hne hm
  exact idxOf_lt_of_sorted _ hpair hwmem hw'mem hlt

include hWF hne hmo in
theorem readoffS_mrank_top {m : Nat} (hm : m < 6) {w w' : Nat}
    (hw : w < 6) (hw' : w' < 6) (hsw : stab I m w = true)
    (hsw' : stab I m w' = false) :
    get2 (readoffS (chainSched I)).mrank m w
      < get2 (readoffS (chainSched I)).mrank m w' := by
  rw [get2_readoffS_mrank hm hw, get2_readoffS_mrank hm hw']
  have hwmem : w ∈ strajM (chainSched I) m :=
    (mem_traj_prefix hWF hne hmo hm hw).2 hsw
  have hw'not : w' ∉ strajM (chainSched I) m := by
    intro hc
    rw [(mem_traj_prefix hWF hne hmo hm hw').1 hc] at hsw'
    exact absurd hsw' (by decide)
  unfold rowOrderM
  rw [idxOf_append_mem hwmem, idxOf_append_notMem hw'not]
  have := idxOf_lt_length hwmem
  omega

end

section
variable {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ [])
  (hmo : manOpt I = idRow6)

include hWF hne hmo in
theorem readoffS_wrank_mono {w : Nat} (hw : w < 6) {m m' : Nat}
    (hm : m < 6) (hm' : m' < 6) (hsm : stab I m w = true)
    (hsm' : stab I m' w = true)
    (hlt : get2 I.wrank w m < get2 I.wrank w m') :
    get2 (readoffS (chainSched I)).wrank w m
      < get2 (readoffS (chainSched I)).wrank w m' := by
  rw [get2_readoffS_wrank hw hm, get2_readoffS_wrank hw hm']
  have hmw : m ∈ wtraj I w := (wtraj_mem_iff hWF hne hw hm).2 hsm
  have hm'w : m' ∈ wtraj I w := (wtraj_mem_iff hWF hne hw hm').2 hsm'
  have hmrev : m ∈ (strajW (chainSched I) w).reverse := by
    rw [strajW_eq_wtraj hWF hne hmo hw, List.mem_reverse]; exact hmw
  have hm'rev : m' ∈ (strajW (chainSched I) w).reverse := by
    rw [strajW_eq_wtraj hWF hne hmo hw, List.mem_reverse]; exact hm'w
  unfold rowOrderW
  rw [idxOf_append_mem hmrev, idxOf_append_mem hm'rev]
  have hpair : ((strajW (chainSched I) w).reverse).Pairwise
      (fun a b => get2 I.wrank w a < get2 I.wrank w b) := by
    rw [strajW_eq_wtraj hWF hne hmo hw, List.pairwise_reverse]
    exact wtraj_rank_pairwise hWF hne hw
  exact idxOf_lt_of_sorted _ hpair hmrev hm'rev hlt

include hWF hne hmo in
/-- **The Validity Lemma** (order-6, `manOpt = idRow6` form): every
instance is dominated in stable-matching count by the read-off instance
of its own chain schedule. -/
theorem sc_le_readoffS_chainSched :
    stableCount6 I ≤ stableCount6 (readoffS (chainSched I)) := by
  refine count_le_of_orderPreserving hWF ?_ ?_ ?_
  · intro m hm w hw w' hw' hsw hsw' hlt
    exact readoffS_mrank_mono hWF hne hmo hm hw hw' hsw hsw' hlt
  · intro m hm w hw w' hw' hsw hsw'
    exact readoffS_mrank_top hWF hne hmo hm hw hw' hsw hsw'
  · intro w hw m hm m' hm' hsm hsm' hlt
    exact readoffS_wrank_mono hWF hne hmo hw hm hm' hsm hsm' hlt

end
