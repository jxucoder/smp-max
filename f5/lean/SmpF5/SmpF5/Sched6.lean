import SmpF5.Sym6

/-!
# Schedules and their read-off instances (order 6)

A schedule is a list of steps; a step is a cyclic move on `k ≥ 2`
distinct men: man `st[i]` takes the current wife of `st[(i+1) % k]`.
Applied from the identity matching, a schedule generates a matching
sequence; each person's destuttered partner column is their trajectory,
and the read-off instance ranks trajectories first (women's reversed),
remaining partners in canonical order. Legality is trajectory
`Nodup` on both sides — the budget caps of Definition 1 are implied.
-/

def applyStep (st mu : List Nat) : List Nat :=
  (List.range 6).map fun m =>
    if m ∈ st then mu.getD (st.getD ((idxOf m st + 1) % st.length) 0) 0
    else mu.getD m 0

def schedMatchings (S : List (List Nat)) : List (List Nat) :=
  S.scanl (fun mu st => applyStep st mu) idRow6

def WFStep (st : List Nat) : Prop :=
  2 ≤ st.length ∧ st.Nodup ∧ ∀ m ∈ st, m < 6

/-- Generic: a 6-element duplicate-free list of values `< 6` is a
permutation of `idRow6`. -/
theorem perm6_of_nodup_lt {l : List Nat} (hlen : l.length = 6)
    (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < 6) : l.Perm idRow6 := by
  have hsub : l ⊆ idRow6 := by
    intro x hx
    have := hlt x hx
    simp only [idRow6, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hsp : l.Subperm idRow6 := hnd.subperm hsub
  have hlen' : idRow6.length ≤ l.length := by simp [idRow6, hlen]
  exact hsp.perm_of_length_le hlen'

theorem succ_mod_inj {L a b : Nat} (ha : a < L) (hb : b < L)
    (h : (a + 1) % L = (b + 1) % L) : a = b := by
  rcases Nat.lt_or_ge (a + 1) L with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    rcases Nat.lt_or_ge (b + 1) L with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h
      omega
    · have hbL : b + 1 = L := by omega
      rw [hbL, Nat.mod_self] at h
      omega
  · have haL : a + 1 = L := by omega
    rw [haL, Nat.mod_self] at h
    rcases Nat.lt_or_ge (b + 1) L with h2 | h2
    · rw [Nat.mod_eq_of_lt h2] at h
      omega
    · omega

/-- The cyclic-successor position is valid. -/
theorem step_succ_pos_lt {st : List Nat} (h2 : 2 ≤ st.length) {i : Nat} :
    (i + 1) % st.length < st.length :=
  Nat.mod_lt _ (by omega)

/-- The cyclic successor of a step member is a step member. -/
theorem step_succ_mem {st : List Nat} (h2 : 2 ≤ st.length) {m : Nat}
    (hm : m ∈ st) : st.getD ((idxOf m st + 1) % st.length) 0 ∈ st := by
  have hlt := step_succ_pos_lt h2 (i := idxOf m st)
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

/-- The cyclic-successor map (identity off the step) is injective on
`{m | m < 6}`. -/
theorem step_succ_inj {st : List Nat} (hst : WFStep st) {a b : Nat}
    (hsucc :
      (if a ∈ st then st.getD ((idxOf a st + 1) % st.length) 0 else a) =
      (if b ∈ st then st.getD ((idxOf b st + 1) % st.length) 0 else b)) :
    a = b := by
  obtain ⟨h2, hnd, _⟩ := hst
  by_cases ha : a ∈ st <;> by_cases hb : b ∈ st
  · rw [if_pos ha, if_pos hb] at hsucc
    have hia : idxOf a st < st.length := idxOf_lt_length ha
    have hib : idxOf b st < st.length := idxOf_lt_length hb
    have hpa := step_succ_pos_lt h2 (i := idxOf a st)
    have hpb := step_succ_pos_lt h2 (i := idxOf b st)
    have h1 : idxOf (st.getD ((idxOf a st + 1) % st.length) 0) st
        = (idxOf a st + 1) % st.length := idxOf_getD hnd hpa
    have h2' : idxOf (st.getD ((idxOf b st + 1) % st.length) 0) st
        = (idxOf b st + 1) % st.length := idxOf_getD hnd hpb
    have heq : (idxOf a st + 1) % st.length
        = (idxOf b st + 1) % st.length := by
      rw [← h1, ← h2', hsucc]
    have := succ_mod_inj hia hib heq
    have hga : st.getD (idxOf a st) 0 = a := getD_idxOf ha
    have hgb : st.getD (idxOf b st) 0 = b := getD_idxOf hb
    rw [← hga, ← hgb, this]
  · rw [if_pos ha, if_neg hb] at hsucc
    exact absurd (hsucc ▸ step_succ_mem h2 ha) hb
  · rw [if_neg ha, if_pos hb] at hsucc
    exact absurd (hsucc.symm ▸ step_succ_mem h2 hb) ha
  · rw [if_neg ha, if_neg hb] at hsucc
    exact hsucc

theorem applyStep_getD {st mu : List Nat} {m : Nat} (hm : m < 6) :
    (applyStep st mu).getD m 0 =
      if m ∈ st then mu.getD (st.getD ((idxOf m st + 1) % st.length) 0) 0
      else mu.getD m 0 := by
  unfold applyStep
  rw [getD_map_range6 hm]

theorem applyStep_perm {st mu : List Nat} (hst : WFStep st)
    (hmu : mu.Perm idRow6) : (applyStep st mu).Perm idRow6 := by
  obtain ⟨h2, hnd, hlt6⟩ := hst
  refine perm6_of_nodup_lt (by simp [applyStep]) ?_ ?_
  · refine List.Nodup.map_on ?_ (List.nodup_range)
    intro x hx y hy heq
    simp only [List.mem_range] at hx hy
    have hgx : (if x ∈ st then st.getD ((idxOf x st + 1) % st.length) 0
        else x) < 6 := by
      split
      · next h => exact hlt6 _ (step_succ_mem h2 h)
      · exact hx
    have hgy : (if y ∈ st then st.getD ((idxOf y st + 1) % st.length) 0
        else y) < 6 := by
      split
      · next h => exact hlt6 _ (step_succ_mem h2 h)
      · exact hy
    have hgd : mu.getD (if x ∈ st then
          st.getD ((idxOf x st + 1) % st.length) 0 else x) 0
        = mu.getD (if y ∈ st then
          st.getD ((idxOf y st + 1) % st.length) 0 else y) 0 := by
      split at heq <;> split at heq <;> simp_all
    have := perm6_getD_inj hmu hgx hgy hgd
    exact step_succ_inj ⟨h2, hnd, hlt6⟩ this
  · intro v hv
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hv
    simp only [List.mem_range] at hm
    split
    · next h => exact perm6_getD_lt hmu (hlt6 _ (step_succ_mem h2 h))
    · exact perm6_getD_lt hmu hm

/-! ## The matching sequence -/

theorem schedMatchings_cons (st : List Nat) (S : List (List Nat)) :
    schedMatchings (st :: S) =
      idRow6 :: (S.scanl (fun mu s => applyStep s mu) (applyStep st idRow6)) := by
  unfold schedMatchings
  rw [List.scanl_cons]

theorem scanl_all_perm :
    ∀ (S : List (List Nat)) (start : List Nat), start.Perm idRow6 →
    (∀ st ∈ S, WFStep st) →
    ∀ mu ∈ S.scanl (fun mu st => applyStep st mu) start, mu.Perm idRow6 := by
  intro S
  induction S with
  | nil =>
    intro start hstart _ mu hmu
    simp only [List.scanl_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hmu
    exact hmu ▸ hstart
  | cons st rest ih =>
    intro start hstart hWF mu hmu
    rw [List.scanl_cons] at hmu
    rcases List.mem_cons.1 hmu with rfl | hmu'
    · exact hstart
    · exact ih _ (applyStep_perm (hWF st List.mem_cons_self) hstart)
        (fun s hs => hWF s (List.mem_cons_of_mem _ hs)) mu hmu'

theorem schedMatchings_perm {S : List (List Nat)}
    (hWF : ∀ st ∈ S, WFStep st) :
    ∀ mu ∈ schedMatchings S, mu.Perm idRow6 :=
  scanl_all_perm S idRow6 (List.Perm.refl _) hWF

theorem schedMatchings_head (S : List (List Nat)) :
    (schedMatchings S).head? = some idRow6 := by
  unfold schedMatchings
  cases S with
  | nil => rfl
  | cons st rest => rw [List.scanl_cons]; rfl

/-! ## Trajectories and legality -/

def strajM (S : List (List Nat)) (m : Nat) : List Nat :=
  ((schedMatchings S).map (fun mu => mu.getD m 0)).destutter (· ≠ ·)

def strajW (S : List (List Nat)) (w : Nat) : List Nat :=
  ((schedMatchings S).map (fun mu => idxOf w mu)).destutter (· ≠ ·)

/-- Legality: well-formed steps and revisit-free trajectories on both
sides. The per-man cap (≤ 5 moves), total budget (≤ 30) and step-count
bound (≤ 15) of Definition 1 are all implied. -/
def Legal (S : List (List Nat)) : Prop :=
  (∀ st ∈ S, WFStep st) ∧
  (∀ m, m < 6 → (strajM S m).Nodup) ∧
  (∀ w, w < 6 → (strajW S w).Nodup)

theorem strajM_all_lt6 {S : List (List Nat)}
    (hWF : ∀ st ∈ S, WFStep st) {m : Nat} (hm : m < 6) :
    ∀ w ∈ strajM S m, w < 6 := by
  intro w hw
  have hcol : w ∈ (schedMatchings S).map (fun mu => mu.getD m 0) :=
    (List.destutter_sublist _ _).subset hw
  obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hcol
  exact perm6_getD_lt (schedMatchings_perm hWF mu hmu) hm

theorem strajW_all_lt6 {S : List (List Nat)}
    (hWF : ∀ st ∈ S, WFStep st) {w : Nat} (hw : w < 6) :
    ∀ m ∈ strajW S w, m < 6 := by
  intro m hm
  have hcol : m ∈ (schedMatchings S).map (fun mu => idxOf w mu) :=
    (List.destutter_sublist _ _).subset hm
  obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hcol
  exact idxOf_lt6 (schedMatchings_perm hWF mu hmu) hw

/-! ## The read-off instance -/

def rankOfOrder (order : List Nat) : List Nat :=
  (List.range 6).map fun x => idxOf x order

def rowOrderM (S : List (List Nat)) (m : Nat) : List Nat :=
  strajM S m ++
    (List.range 6).filter (fun w => decide (w ∉ strajM S m))

def rowOrderW (S : List (List Nat)) (w : Nat) : List Nat :=
  (strajW S w).reverse ++
    (List.range 6).filter (fun m => decide (m ∉ (strajW S w).reverse))

def readoffS (S : List (List Nat)) : Inst6 :=
  ⟨(List.range 6).map fun m => rankOfOrder (rowOrderM S m),
   (List.range 6).map fun w => rankOfOrder (rowOrderW S w)⟩

/-- A duplicate-free partial list of `0..5` completed by the missing
values is a permutation of `idRow6`. -/
theorem rowOrder_perm {tr : List Nat} (hnd : tr.Nodup)
    (hlt : ∀ x ∈ tr, x < 6) :
    (tr ++ (List.range 6).filter (fun w => decide (w ∉ tr))).Perm
      idRow6 := by
  have hndf : ((List.range 6).filter
      (fun w => decide (w ∈ tr))).Nodup := List.nodup_range.filter _
  have h1 : tr.Perm ((List.range 6).filter (fun w => decide (w ∈ tr))) := by
    rw [List.perm_ext_iff_of_nodup hnd hndf]
    intro x
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun hx => ⟨hlt x hx, hx⟩, fun h => h.2⟩
  have h2 := List.filter_append_perm
    (fun w => decide (w ∈ tr)) (List.range 6)
  have h3 : (List.range 6).filter (fun w => !decide (w ∈ tr))
      = (List.range 6).filter (fun w => decide (w ∉ tr)) := by
    apply List.filter_congr
    intro x _
    simp
  rw [h3] at h2
  rw [idRow6_eq_range]
  exact (h1.append (List.Perm.refl _)).trans h2

theorem isRankRow6_rankOfOrder {order : List Nat}
    (hp : order.Perm idRow6) :
    isRankRow6 (rankOfOrder order) = true := by
  simp only [isRankRow6, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  constructor
  · simp [rankOfOrder]
  · intro v hv
    rw [List.contains_iff_mem]
    refine List.mem_map.2 ⟨order.getD v 0, ?_, ?_⟩
    · simp only [List.mem_range]
      exact perm6_getD_lt hp hv
    · exact idxOf_getD (hp.nodup_iff.2 (by decide))
        (by rw [perm6_length hp]; exact hv)

theorem rowOrderM_perm {S : List (List Nat)} (hL : Legal S) {m : Nat}
    (hm : m < 6) : (rowOrderM S m).Perm idRow6 :=
  rowOrder_perm (hL.2.1 m hm) (strajM_all_lt6 hL.1 hm)

theorem rowOrderW_perm {S : List (List Nat)} (hL : Legal S) {w : Nat}
    (hw : w < 6) : (rowOrderW S w).Perm idRow6 := by
  refine rowOrder_perm (List.nodup_reverse.2 (hL.2.2 w hw)) ?_
  intro x hx
  exact strajW_all_lt6 hL.1 hw x (List.mem_reverse.1 hx)

/-- The read-off instance of a legal schedule is well-formed. -/
theorem WF6_readoffS {S : List (List Nat)} (hL : Legal S) :
    WF6 (readoffS S) = true := by
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨by simp [readoffS], by simp [readoffS]⟩, ?_⟩, ?_⟩
  · intro r hr
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hr
    have hm6 : m < 6 := by simpa using hm
    exact isRankRow6_rankOfOrder (rowOrderM_perm hL hm6)
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have hw6 : w < 6 := by simpa using hw
    exact isRankRow6_rankOfOrder (rowOrderW_perm hL hw6)
