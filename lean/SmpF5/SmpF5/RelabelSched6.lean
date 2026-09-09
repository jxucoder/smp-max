import SmpF5.WRelabel6
import SmpF5.Cubes6

/-!
# Schedule-level relabeling (plan §3.1–§3.2, §3.4)

`relabelSched σ S` renames every man in every step by `app σ`; men and
women are relabeled by the same `σ`, matching `relabel6 σ` and `mapMu6`.
The definition comes first; the equivariance, legality and count-bridge
lemmas (L3.1–L3.7, L3.12–L3.16) follow below it.

Implemented here (`docs/history/f6-FAITHFULNESS_PLAN.md`):

* §3.2 — L3.1 `mapMu6_idRow6`, L3.2 `applyStep_relabel`,
  L3.3 `schedMatchings_relabel`, L3.4 `strajM_relabel`,
  L3.5 `strajW_relabel`, L3.6 `WFStep_relabel` / `relabelSched_WF` /
  `Legal_relabel`, L3.7 `length_relabelSched`.
* §3.4 — L3.12 `stab_relabel6`, L3.13 `readoffS_relabel_mrank_mono`,
  L3.14 `readoffS_relabel_mrank_top`, L3.15 `readoffS_relabel_wrank_mono`,
  L3.16 `sc_le_readoffS_relabelSched`.

`readoffS` is *not* relabel-equivariant (its bottom completion is in
ascending label order), so the bridge is re-instantiated at the relabeled
instance `relabel6 σ J` against `readoffS (relabelSched σ (chainSched J))`
via `count_le_of_orderPreserving`; no equation
`readoffS (relabelSched σ S) = relabel6 σ (readoffS S)` is stated.

Deviations from the plan statements: none. (`relabelSched_WF` carries the
hypothesis `σ.Perm idRow6`, which the plan's one-line sketch omitted; it is
needed for the `< 6` bound of relabeled men.)
-/

def relabelSched (σ : List Nat) (S : List (List Nat)) : List (List Nat) :=
  S.map (fun st => st.map (app σ))

theorem length_relabelSched (σ : List Nat) (S : List (List Nat)) :
    (relabelSched σ S).length = S.length := by
  simp [relabelSched]

/-! ## Helpers (private namespace) -/

namespace RelabelSched6

/-- Every label `< 6` is `app σ` of a label `< 6`. -/
theorem exists_preimage {σ : List Nat} (hp : σ.Perm idRow6) {m' : Nat}
    (hm' : m' < 6) : ∃ m, m < 6 ∧ m' = app σ m :=
  ⟨app (invMatch σ) m', inv_app_lt6 hp hm', (app_inv_app6 hp hm').symm⟩

/-- `mapMu6 σ` is a right inverse of `mapMu6 (invMatch σ)`. -/
theorem mapMu6_right_inv {σ nu : List Nat} (hp : σ.Perm idRow6)
    (hnu : nu.Perm idRow6) :
    mapMu6 σ (mapMu6 (invMatch σ) nu) = nu := by
  have h := mapMu6_left_inv (invMatch_perm hp) hnu
  rwa [invMatch_invMatch hp] at h

/-- Transport of stable-matching membership along `mapMu6 σ`. -/
theorem mem_sms6_mapMu6_iff {σ : List Nat} (hp : σ.Perm idRow6) {J : Inst6}
    {mu : List Nat} (hmu : mu.Perm idRow6) :
    mapMu6 σ mu ∈ sms6 (relabel6 σ J) ↔ mu ∈ sms6 J := by
  unfold sms6
  rw [List.mem_filter, List.mem_filter, List.mem_permutations,
    List.mem_permutations, isStable6_relabel6 hp hmu]
  exact ⟨fun h => ⟨hmu, h.2⟩, fun h => ⟨mapMu6_perm hp hmu, h.2⟩⟩

end RelabelSched6

open RelabelSched6

/-! ## L3.1: the identity matching is fixed -/

theorem mapMu6_idRow6 {σ : List Nat} (hp : σ.Perm idRow6) :
    mapMu6 σ idRow6 = idRow6 := by
  refine perm6_ext (mapMu6_perm hp (List.Perm.refl _)) (List.Perm.refl _) ?_
  intro x hx
  rw [mapMu6_getD hx, idRow6_getD6 hx]
  show app σ (idRow6.getD (app (invMatch σ) x) 0) = x
  rw [idRow6_getD6 (inv_app_lt6 hp hx)]
  exact app_inv_app6 hp hx

/-! ## L3.6 (steps): well-formedness of relabeled steps -/

theorem WFStep_relabel {σ st : List Nat} (hp : σ.Perm idRow6)
    (hst : WFStep st) : WFStep (st.map (app σ)) := by
  obtain ⟨h2, hnd, hlt6⟩ := hst
  refine ⟨by simpa using h2, ?_, ?_⟩
  · exact hnd.map_on (fun x hx y hy h => app_inj6 hp (hlt6 x hx) (hlt6 y hy) h)
  · intro m' hm'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hm'
    exact app_lt6 hp (hlt6 m hm)

theorem relabelSched_WF {σ : List Nat} (hp : σ.Perm idRow6)
    {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    ∀ st ∈ relabelSched σ S, WFStep st := by
  intro st' hst'
  obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hst'
  exact WFStep_relabel hp (hWF st hst)

/-! ## L3.2: one step commutes with relabeling -/

theorem applyStep_relabel {σ st mu : List Nat} (hp : σ.Perm idRow6)
    (hst : WFStep st) (hmu : mu.Perm idRow6) :
    applyStep (st.map (app σ)) (mapMu6 σ mu) = mapMu6 σ (applyStep st mu) := by
  have hst' : WFStep (st.map (app σ)) := WFStep_relabel hp hst
  have h2 : 2 ≤ st.length := hst.1
  have hlt6 : ∀ m ∈ st, m < 6 := hst.2.2
  refine perm6_ext (applyStep_perm hst' (mapMu6_perm hp hmu))
    (mapMu6_perm hp (applyStep_perm hst hmu)) ?_
  intro m' hm'
  obtain ⟨m, hm, rfl⟩ := exists_preimage hp hm'
  have hR : (mapMu6 σ (applyStep st mu)).getD (app σ m) 0
      = app σ ((applyStep st mu).getD m 0) := by
    rw [mapMu6_getD hm', inv_app_app6 hp hm]
    rfl
  rw [hR, applyStep_getD hm', applyStep_getD hm]
  by_cases hmem : m ∈ st
  · have hmem' : app σ m ∈ st.map (app σ) := List.mem_map.2 ⟨m, hmem, rfl⟩
    rw [if_pos hmem', if_pos hmem]
    have hidx : idxOf (app σ m) (st.map (app σ)) = idxOf m st :=
      idxOf_map (fun y hy h => app_inj6 hp (hlt6 y hy) hm h)
    rw [hidx, List.length_map]
    have hklt : (idxOf m st + 1) % st.length < st.length := step_succ_pos_lt h2
    rw [getD_map_nat hklt]
    have hsucc6 : st.getD ((idxOf m st + 1) % st.length) 0 < 6 :=
      hlt6 _ (step_succ_mem h2 hmem)
    rw [mapMu6_getD (app_lt6 hp hsucc6), inv_app_app6 hp hsucc6]
    rfl
  · have hmem' : app σ m ∉ st.map (app σ) := by
      intro hc
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hc
      exact hmem ((app_inj6 hp (hlt6 y hy) hm hyx) ▸ hy)
    rw [if_neg hmem', if_neg hmem, mapMu6_getD hm', inv_app_app6 hp hm]
    rfl

/-! ## L3.3: the matching sequence -/

theorem scanl_relabel {σ : List Nat} (hp : σ.Perm idRow6) :
    ∀ (S : List (List Nat)) (start : List Nat), start.Perm idRow6 →
    (∀ st ∈ S, WFStep st) →
    (S.map (fun st => st.map (app σ))).scanl
        (fun mu st => applyStep st mu) (mapMu6 σ start)
      = (S.scanl (fun mu st => applyStep st mu) start).map (mapMu6 σ) := by
  intro S
  induction S with
  | nil => intro start _ _; simp
  | cons st rest ih =>
    intro start hstart hWF
    simp only [List.map_cons, List.scanl_cons]
    rw [applyStep_relabel hp (hWF st List.mem_cons_self) hstart]
    rw [ih _ (applyStep_perm (hWF st List.mem_cons_self) hstart)
      (fun s hs => hWF s (List.mem_cons_of_mem _ hs))]

theorem schedMatchings_relabel {σ : List Nat} (hp : σ.Perm idRow6)
    {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    schedMatchings (relabelSched σ S) = (schedMatchings S).map (mapMu6 σ) := by
  unfold schedMatchings relabelSched
  have h := scanl_relabel hp S idRow6 (List.Perm.refl _) hWF
  rw [mapMu6_idRow6 hp] at h
  exact h

/-! ## L3.4 / L3.5: trajectories -/

theorem strajM_relabel {σ : List Nat} (hp : σ.Perm idRow6)
    {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) {m : Nat} (hm : m < 6) :
    strajM (relabelSched σ S) (app σ m) = (strajM S m).map (app σ) := by
  unfold strajM
  rw [schedMatchings_relabel hp hWF, List.map_map]
  have hcol : (schedMatchings S).map ((fun mu => mu.getD (app σ m) 0) ∘ mapMu6 σ)
      = ((schedMatchings S).map (fun mu => mu.getD m 0)).map (app σ) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro mu _
    show (mapMu6 σ mu).getD (app σ m) 0 = app σ (mu.getD m 0)
    rw [mapMu6_getD (app_lt6 hp hm), inv_app_app6 hp hm]
    rfl
  rw [hcol]
  symm
  apply List.map_destutter
  intro a ha b hb
  have ha6 : a < 6 := by
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 ha
    exact perm6_getD_lt (schedMatchings_perm hWF mu hmu) hm
  have hb6 : b < 6 := by
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hb
    exact perm6_getD_lt (schedMatchings_perm hWF mu hmu) hm
  constructor
  · intro hne h
    exact hne (app_inj6 hp ha6 hb6 h)
  · intro hne h
    exact hne (h ▸ rfl)

theorem strajW_relabel {σ : List Nat} (hp : σ.Perm idRow6)
    {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) {w : Nat} (hw : w < 6) :
    strajW (relabelSched σ S) (app σ w) = (strajW S w).map (app σ) := by
  unfold strajW
  rw [schedMatchings_relabel hp hWF, List.map_map]
  have hcol : (schedMatchings S).map ((fun mu => idxOf (app σ w) mu) ∘ mapMu6 σ)
      = ((schedMatchings S).map (fun mu => idxOf w mu)).map (app σ) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro mu hmu
    show idxOf (app σ w) (mapMu6 σ mu) = app σ (idxOf w mu)
    rw [mapMu6_idxOf hp (schedMatchings_perm hWF mu hmu) (app_lt6 hp hw),
      inv_app_app6 hp hw]
  rw [hcol]
  symm
  apply List.map_destutter
  intro a ha b hb
  have ha6 : a < 6 := by
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 ha
    exact idxOf_lt6 (schedMatchings_perm hWF mu hmu) hw
  have hb6 : b < 6 := by
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hb
    exact idxOf_lt6 (schedMatchings_perm hWF mu hmu) hw
  constructor
  · intro hne h
    exact hne (app_inj6 hp ha6 hb6 h)
  · intro hne h
    exact hne (h ▸ rfl)

/-! ## L3.6: legality -/

theorem Legal_relabel {σ : List Nat} (hp : σ.Perm idRow6) {S : List (List Nat)}
    (hL : Legal S) : Legal (relabelSched σ S) := by
  obtain ⟨hWF, hM, hW⟩ := hL
  refine ⟨relabelSched_WF hp hWF, ?_, ?_⟩
  · intro m' hm'
    obtain ⟨m, hm, rfl⟩ := exists_preimage hp hm'
    rw [strajM_relabel hp hWF hm]
    exact (hM m hm).map_on (fun x hx y hy h =>
      app_inj6 hp (strajM_all_lt6 hWF hm x hx) (strajM_all_lt6 hWF hm y hy) h)
  · intro w' hw'
    obtain ⟨w, hw, rfl⟩ := exists_preimage hp hw'
    rw [strajW_relabel hp hWF hw]
    exact (hW w hw).map_on (fun x hx y hy h =>
      app_inj6 hp (strajW_all_lt6 hWF hw x hx) (strajW_all_lt6 hWF hw y hy) h)

/-! ## L3.12: stable pairs transport -/

theorem stab_relabel6 {σ : List Nat} (hp : σ.Perm idRow6) {J : Inst6}
    {m w : Nat} (hm : m < 6) (hw : w < 6) :
    stab (relabel6 σ J) (app σ m) (app σ w) = stab J m w := by
  rw [Bool.eq_iff_iff]
  simp only [stab, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨nu, hnu, hval⟩
    have hnup : nu.Perm idRow6 := mem_sms6_perm hnu
    refine ⟨mapMu6 (invMatch σ) nu, ?_, ?_⟩
    · have h := mem_sms6_mapMu6_iff hp (J := J)
        (mapMu6_perm (invMatch_perm hp) hnup)
      rw [mapMu6_right_inv hp hnup] at h
      exact h.1 hnu
    · rw [mapMu6_getD hm, invMatch_invMatch hp]
      show app (invMatch σ) (nu.getD (app σ m) 0) = w
      rw [hval]
      exact inv_app_app6 hp hw
  · rintro ⟨mu, hmu, hval⟩
    have hmup : mu.Perm idRow6 := mem_sms6_perm hmu
    refine ⟨mapMu6 σ mu, (mem_sms6_mapMu6_iff hp hmup).2 hmu, ?_⟩
    rw [mapMu6_getD (app_lt6 hp hm), inv_app_app6 hp hm]
    show app σ (mu.getD m 0) = app σ w
    rw [hval]

/-! ## L3.13–L3.15: order preservation at the relabeled schedule -/

section
variable {J : Inst6} (hWF : WF6 J = true) (hne : sms6 J ≠ [])
  (hmo : manOpt J = idRow6) {σ : List Nat} (hp : σ.Perm idRow6)

include hWF hne hmo hp in
theorem readoffS_relabel_mrank_mono {m : Nat} (hm : m < 6) {w w' : Nat}
    (hw : w < 6) (hw' : w' < 6) (hsw : stab (relabel6 σ J) m w = true)
    (hsw' : stab (relabel6 σ J) m w' = true)
    (hlt : get2 (relabel6 σ J).mrank m w < get2 (relabel6 σ J).mrank m w') :
    get2 (readoffS (relabelSched σ (chainSched J))).mrank m w
      < get2 (readoffS (relabelSched σ (chainSched J))).mrank m w' := by
  have hWFS : ∀ st ∈ chainSched J, WFStep st := (Legal_chainSched hWF hne hmo).1
  obtain ⟨m0, hm0, rfl⟩ := exists_preimage hp hm
  obtain ⟨w0, hw0, rfl⟩ := exists_preimage hp hw
  obtain ⟨w0', hw0', rfl⟩ := exists_preimage hp hw'
  rw [stab_relabel6 hp hm0 hw0] at hsw
  rw [stab_relabel6 hp hm0 hw0'] at hsw'
  rw [get2_relabel6_m hm hw, get2_relabel6_m hm hw', inv_app_app6 hp hm0,
    inv_app_app6 hp hw0, inv_app_app6 hp hw0'] at hlt
  rw [get2_readoffS_mrank hm hw, get2_readoffS_mrank hm hw']
  unfold rowOrderM
  rw [strajM_relabel hp hWFS hm0]
  have hw0mem : w0 ∈ strajM (chainSched J) m0 :=
    (mem_traj_prefix hWF hne hmo hm0 hw0).2 hsw
  have hw0'mem : w0' ∈ strajM (chainSched J) m0 :=
    (mem_traj_prefix hWF hne hmo hm0 hw0').2 hsw'
  have hwmem : app σ w0 ∈ (strajM (chainSched J) m0).map (app σ) :=
    List.mem_map.2 ⟨w0, hw0mem, rfl⟩
  have hw'mem : app σ w0' ∈ (strajM (chainSched J) m0).map (app σ) :=
    List.mem_map.2 ⟨w0', hw0'mem, rfl⟩
  rw [idxOf_append_mem hwmem, idxOf_append_mem hw'mem]
  have hlt6 := strajM_all_lt6 hWFS hm0
  rw [idxOf_map (fun y hy h => app_inj6 hp (hlt6 y hy) hw0 h),
    idxOf_map (fun y hy h => app_inj6 hp (hlt6 y hy) hw0' h)]
  have hpair : (strajM (chainSched J) m0).Pairwise
      (fun a b => get2 J.mrank m0 a < get2 J.mrank m0 b) := by
    rw [strajM_eq_traj hWF hne hmo hm0]
    exact traj_rank_pairwise hWF hne hm0
  exact idxOf_lt_of_sorted _ hpair hw0mem hw0'mem hlt

include hWF hne hmo hp in
theorem readoffS_relabel_mrank_top {m : Nat} (hm : m < 6) {w w' : Nat}
    (hw : w < 6) (hw' : w' < 6) (hsw : stab (relabel6 σ J) m w = true)
    (hsw' : stab (relabel6 σ J) m w' = false) :
    get2 (readoffS (relabelSched σ (chainSched J))).mrank m w
      < get2 (readoffS (relabelSched σ (chainSched J))).mrank m w' := by
  have hWFS : ∀ st ∈ chainSched J, WFStep st := (Legal_chainSched hWF hne hmo).1
  obtain ⟨m0, hm0, rfl⟩ := exists_preimage hp hm
  obtain ⟨w0, hw0, rfl⟩ := exists_preimage hp hw
  obtain ⟨w0', hw0', rfl⟩ := exists_preimage hp hw'
  rw [stab_relabel6 hp hm0 hw0] at hsw
  rw [stab_relabel6 hp hm0 hw0'] at hsw'
  rw [get2_readoffS_mrank hm hw, get2_readoffS_mrank hm hw']
  unfold rowOrderM
  rw [strajM_relabel hp hWFS hm0]
  have hw0mem : w0 ∈ strajM (chainSched J) m0 :=
    (mem_traj_prefix hWF hne hmo hm0 hw0).2 hsw
  have hw0'not : w0' ∉ strajM (chainSched J) m0 := by
    intro hc
    rw [(mem_traj_prefix hWF hne hmo hm0 hw0').1 hc] at hsw'
    exact absurd hsw' (by decide)
  have hlt6 := strajM_all_lt6 hWFS hm0
  have hwmem : app σ w0 ∈ (strajM (chainSched J) m0).map (app σ) :=
    List.mem_map.2 ⟨w0, hw0mem, rfl⟩
  have hw'not : app σ w0' ∉ (strajM (chainSched J) m0).map (app σ) := by
    intro hc
    obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hc
    exact hw0'not ((app_inj6 hp (hlt6 y hy) hw0' hyx) ▸ hy)
  rw [idxOf_append_mem hwmem, idxOf_append_notMem hw'not]
  have := idxOf_lt_length hwmem
  omega

include hWF hne hmo hp in
theorem readoffS_relabel_wrank_mono {w : Nat} (hw : w < 6) {m m' : Nat}
    (hm : m < 6) (hm' : m' < 6) (hsm : stab (relabel6 σ J) m w = true)
    (hsm' : stab (relabel6 σ J) m' w = true)
    (hlt : get2 (relabel6 σ J).wrank w m < get2 (relabel6 σ J).wrank w m') :
    get2 (readoffS (relabelSched σ (chainSched J))).wrank w m
      < get2 (readoffS (relabelSched σ (chainSched J))).wrank w m' := by
  have hWFS : ∀ st ∈ chainSched J, WFStep st := (Legal_chainSched hWF hne hmo).1
  obtain ⟨w0, hw0, rfl⟩ := exists_preimage hp hw
  obtain ⟨m0, hm0, rfl⟩ := exists_preimage hp hm
  obtain ⟨m0', hm0', rfl⟩ := exists_preimage hp hm'
  rw [stab_relabel6 hp hm0 hw0] at hsm
  rw [stab_relabel6 hp hm0' hw0] at hsm'
  rw [get2_relabel6_w hw hm, get2_relabel6_w hw hm', inv_app_app6 hp hw0,
    inv_app_app6 hp hm0, inv_app_app6 hp hm0'] at hlt
  rw [get2_readoffS_wrank hw hm, get2_readoffS_wrank hw hm']
  unfold rowOrderW
  rw [strajW_relabel hp hWFS hw0, ← List.map_reverse]
  have hm0w : m0 ∈ wtraj J w0 := (wtraj_mem_iff hWF hne hw0 hm0).2 hsm
  have hm0'w : m0' ∈ wtraj J w0 := (wtraj_mem_iff hWF hne hw0 hm0').2 hsm'
  have hm0rev : m0 ∈ (strajW (chainSched J) w0).reverse := by
    rw [strajW_eq_wtraj hWF hne hmo hw0, List.mem_reverse]; exact hm0w
  have hm0'rev : m0' ∈ (strajW (chainSched J) w0).reverse := by
    rw [strajW_eq_wtraj hWF hne hmo hw0, List.mem_reverse]; exact hm0'w
  have hmrev : app σ m0 ∈ ((strajW (chainSched J) w0).reverse).map (app σ) :=
    List.mem_map.2 ⟨m0, hm0rev, rfl⟩
  have hm'rev : app σ m0' ∈ ((strajW (chainSched J) w0).reverse).map (app σ) :=
    List.mem_map.2 ⟨m0', hm0'rev, rfl⟩
  rw [idxOf_append_mem hmrev, idxOf_append_mem hm'rev]
  have hlt6 : ∀ x ∈ (strajW (chainSched J) w0).reverse, x < 6 :=
    fun x hx => strajW_all_lt6 hWFS hw0 x (List.mem_reverse.1 hx)
  rw [idxOf_map (fun y hy h => app_inj6 hp (hlt6 y hy) hm0 h),
    idxOf_map (fun y hy h => app_inj6 hp (hlt6 y hy) hm0' h)]
  have hpair : ((strajW (chainSched J) w0).reverse).Pairwise
      (fun a b => get2 J.wrank w0 a < get2 J.wrank w0 b) := by
    rw [strajW_eq_wtraj hWF hne hmo hw0, List.pairwise_reverse]
    exact wtraj_rank_pairwise hWF hne hw0
  exact idxOf_lt_of_sorted _ hpair hm0rev hm0'rev hlt

end

/-! ## L3.16: the bridge at the relabeled schedule -/

theorem sc_le_readoffS_relabelSched {J : Inst6} (hWF : WF6 J = true)
    (hne : sms6 J ≠ []) (hmo : manOpt J = idRow6) {σ : List Nat}
    (hp : σ.Perm idRow6) :
    stableCount6 (relabel6 σ J)
      ≤ stableCount6 (readoffS (relabelSched σ (chainSched J))) := by
  refine count_le_of_orderPreserving (WF6_relabel6 hp hWF) ?_ ?_ ?_
  · intro m hm w hw w' hw' hsw hsw' hlt
    exact readoffS_relabel_mrank_mono hWF hne hmo hp hm hw hw' hsw hsw' hlt
  · intro m hm w hw w' hw' hsw hsw'
    exact readoffS_relabel_mrank_top hWF hne hmo hp hm hw hw' hsw hsw'
  · intro w hw m hm m' hm' hsm hsm' hlt
    exact readoffS_relabel_wrank_mono hWF hne hmo hp hw hm hm' hsm hsm' hlt
