import SmpF5.SchedCNF6
import SmpF5.Sched6

/-!
# Min-first rotation of steps (plan §4.2, part 1: semantics)

The campaign writes every step in min-first cyclic form (an element of
`cyclicShapes 6`); `Legal`/`WFStep` admit any rotation.  Rotating a step
does not change `applyStep`, hence not the matching sequence, the
trajectories, or legality.
-/

/-- Rotate `st` so that it starts at `x` (identity if `x ∉ st`). -/
def rotateTo (st : List Nat) (x : Nat) : List Nat :=
  st.drop (idxOf x st) ++ st.take (idxOf x st)

/-- Min-first form of a step. -/
def minFirst (st : List Nat) : List Nat := rotateTo st (st.foldl min 6)

theorem idxOf_le_length (x : Nat) : ∀ (l : List Nat), idxOf x l ≤ l.length := by
  intro l
  induction l with
  | nil => simp [idxOf]
  | cons y ys ih =>
    simp only [idxOf, List.length_cons]
    split <;> omega

theorem rotateTo_perm (st : List Nat) (x : Nat) : (rotateTo st x).Perm st := by
  unfold rotateTo
  exact (List.perm_append_comm).trans (by rw [List.take_append_drop])

theorem rotateTo_length (st : List Nat) (x : Nat) : (rotateTo st x).length = st.length :=
  (rotateTo_perm st x).length_eq

theorem rotateTo_nodup {st : List Nat} (hnd : st.Nodup) (x : Nat) : (rotateTo st x).Nodup :=
  (rotateTo_perm st x).nodup_iff.2 hnd

theorem mem_rotateTo {st : List Nat} {x m : Nat} : m ∈ rotateTo st x ↔ m ∈ st :=
  (rotateTo_perm st x).mem_iff

/-- Entry `q` of the rotation is entry `(q + r) % L` of the original. -/
theorem rotateTo_getD {st : List Nat} {x q : Nat} (hq : q < st.length) :
    (rotateTo st x).getD q 0 = st.getD ((q + idxOf x st) % st.length) 0 := by
  unfold rotateTo
  set r := idxOf x st with hr
  have hrL : r ≤ st.length := idxOf_le_length x st
  have hdl : (st.drop r).length = st.length - r := List.length_drop
  by_cases hlt : q < st.length - r
  · rw [List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega))]
    rw [List.getElem_drop]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have hlen : (st.take r).length = r := by simp [List.length_take]; omega
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega))]
    rw [List.getElem_take]
    congr 1
    have : (q + r) % st.length = q + r - st.length := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [this]; omega

/-- Position of a member after rotation. -/
theorem idxOf_rotateTo {st : List Nat} (hnd : st.Nodup) {x m : Nat} (hm : m ∈ st) :
    idxOf m (rotateTo st x) = (idxOf m st + st.length - idxOf x st) % st.length := by
  set r := idxOf x st with hr
  set L := st.length with hL
  have hrL : r ≤ L := idxOf_le_length x st
  have hi : idxOf m st < L := idxOf_lt_length hm
  have hL0 : 0 < L := by omega
  set q := (idxOf m st + L - r) % L with hq
  have hqL : q < L := Nat.mod_lt _ hL0
  have hget : (rotateTo st x).getD q 0 = m := by
    rw [rotateTo_getD hqL, ← hr]
    have : (q + r) % L = idxOf m st := by
      rw [hq, Nat.mod_add_mod]
      have e : idxOf m st + L - r + r = idxOf m st + L := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    rw [this]
    exact getD_idxOf hm
  have hnd' := rotateTo_nodup hnd x
  have hqL' : q < (rotateTo st x).length := by rw [rotateTo_length]; exact hqL
  rw [← hget]
  exact idxOf_getD hnd' hqL'

theorem mod_succ_rot {i r L : Nat} (hi : i < L) (hr : r ≤ L) :
    ((i + L - r) % L + 1 + r) % L = (i + 1) % L := by
  have hL0 : 0 < L := by omega
  rw [Nat.add_assoc, Nat.mod_add_mod]
  have e : i + L - r + (1 + r) = i + 1 + L := by omega
  rw [e, Nat.add_mod_right]

/-- The cyclic successor of a member is rotation-invariant. -/
theorem succ_rotateTo {st : List Nat} (hst : WFStep st) {x m : Nat} (hm : m ∈ st) :
    (rotateTo st x).getD ((idxOf m (rotateTo st x) + 1) % (rotateTo st x).length) 0 =
      st.getD ((idxOf m st + 1) % st.length) 0 := by
  obtain ⟨h2, hnd, _⟩ := hst
  rw [rotateTo_length, idxOf_rotateTo hnd hm]
  have hrL : idxOf x st ≤ st.length := idxOf_le_length x st
  have hi : idxOf m st < st.length := idxOf_lt_length hm
  have hL0 : 0 < st.length := by omega
  rw [rotateTo_getD (Nat.mod_lt _ hL0)]
  congr 1
  rw [Nat.mod_add_mod, mod_succ_rot hi hrL]

theorem applyStep_rotate {st : List Nat} (hst : WFStep st) {x : Nat} (mu : List Nat) :
    applyStep (rotateTo st x) mu = applyStep st mu := by
  unfold applyStep
  apply List.map_congr_left
  intro m _
  by_cases hm : m ∈ st
  · rw [if_pos (mem_rotateTo.2 hm), if_pos hm, succ_rotateTo hst hm]
  · rw [if_neg (fun h => hm (mem_rotateTo.1 h)), if_neg hm]

/-! ## The minimum of a step -/

theorem foldl_min_le_init : ∀ (l : List Nat) (a : Nat), l.foldl min a ≤ a := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons b l ih => intro a; simp only [List.foldl_cons]; exact le_trans (ih _) (Nat.min_le_left _ _)

theorem foldl_min_le {l : List Nat} : ∀ (a : Nat), ∀ y ∈ l, l.foldl min a ≤ y := by
  induction l with
  | nil => intro a y hy; exact absurd hy List.not_mem_nil
  | cons b l ih =>
    intro a y hy
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hy with rfl | hy'
    · calc l.foldl min (min a y) ≤ min a y := foldl_min_le_init l (min a y)
        _ ≤ y := Nat.min_le_right _ _
    · exact ih _ y hy'

theorem foldl_min_mem_or {l : List Nat} : ∀ (a : Nat), l.foldl min a = a ∨ l.foldl min a ∈ l := by
  induction l with
  | nil => intro a; simp
  | cons b l ih =>
    intro a
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (min a b) with h | h
    · rw [h]
      rcases Nat.le_total a b with hab | hab
      · left; exact Nat.min_eq_left hab
      · right; left; exact Nat.min_eq_right hab
    · right; right; exact h

theorem stepMin_mem {st : List Nat} (hst : WFStep st) : st.foldl min 6 ∈ st := by
  obtain ⟨h2, _, hlt⟩ := hst
  rcases foldl_min_mem_or (l := st) 6 with h | h
  · exfalso
    obtain ⟨y, hy⟩ : ∃ y, y ∈ st := by
      cases st with
      | nil => simp at h2
      | cons z _ => exact ⟨z, List.mem_cons_self⟩
    have := foldl_min_le (l := st) 6 y hy
    have := hlt y hy
    omega
  · exact h

theorem minFirst_perm {st : List Nat} : (minFirst st).Perm st := rotateTo_perm st _

theorem minFirst_WFStep {st : List Nat} (hst : WFStep st) : WFStep (minFirst st) := by
  obtain ⟨h2, hnd, hlt⟩ := hst
  refine ⟨?_, rotateTo_nodup hnd _, ?_⟩
  · rw [minFirst, rotateTo_length]; exact h2
  · intro m hm; exact hlt m (mem_rotateTo.1 hm)

theorem applyStep_minFirst {st : List Nat} (hst : WFStep st) (mu : List Nat) :
    applyStep (minFirst st) mu = applyStep st mu :=
  applyStep_rotate hst mu

theorem minFirst_head {st : List Nat} (hst : WFStep st) :
    (minFirst st).headD 0 = st.foldl min 6 := by
  have hm := stepMin_mem hst
  have h0 : (minFirst st).getD 0 0 = st.foldl min 6 := by
    unfold minFirst
    rw [rotateTo_getD (by have := hst.1; omega), Nat.zero_add,
      Nat.mod_eq_of_lt (idxOf_lt_length hm)]
    exact getD_idxOf hm
  have hhd : ∀ (l : List Nat), l.headD 0 = l.getD 0 0 := by intro l; cases l <;> rfl
  rw [hhd, h0]

/-! ## Matching sequences and legality are rotation-invariant -/

theorem scanl_map_minFirst : ∀ (S : List (List Nat)) (start : List Nat),
    (∀ st ∈ S, WFStep st) →
    (S.map minFirst).scanl (fun mu st => applyStep st mu) start =
      S.scanl (fun mu st => applyStep st mu) start := by
  intro S
  induction S with
  | nil => intro start _; rfl
  | cons st rest ih =>
    intro start hWF
    simp only [List.map_cons, List.scanl_cons]
    rw [applyStep_minFirst (hWF st List.mem_cons_self)]
    rw [ih _ (fun s hs => hWF s (List.mem_cons_of_mem _ hs))]

theorem schedMatchings_map_minFirst {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    schedMatchings (S.map minFirst) = schedMatchings S :=
  scanl_map_minFirst S idRow6 hWF

theorem strajM_map_minFirst {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) (m : Nat) :
    strajM (S.map minFirst) m = strajM S m := by
  unfold strajM; rw [schedMatchings_map_minFirst hWF]

theorem strajW_map_minFirst {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) (w : Nat) :
    strajW (S.map minFirst) w = strajW S w := by
  unfold strajW; rw [schedMatchings_map_minFirst hWF]

theorem Legal_map_minFirst {S : List (List Nat)} (hL : Legal S) : Legal (S.map minFirst) := by
  obtain ⟨hWF, hM, hW⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · intro st hst
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hst
    exact minFirst_WFStep (hWF s hs)
  · intro m hm; rw [strajM_map_minFirst hWF]; exact hM m hm
  · intro w hw; rw [strajW_map_minFirst hWF]; exact hW w hw

theorem length_map_minFirst (S : List (List Nat)) : (S.map minFirst).length = S.length :=
  List.length_map ..
