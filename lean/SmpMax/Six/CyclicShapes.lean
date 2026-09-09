import SmpMax.Six.ScheduleEncoding
import SmpMax.Six.Schedule

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

/-! ## Enumerations (plan §4.2 part 2, §4.3): `combos`, `permsOf`, `cyclicShapes`, `permsN` -/

open SchedCNF6

theorem mem_combos : ∀ (xs : List Nat) (k : Nat) (l : List Nat),
    l ∈ combos xs k ↔ l.Sublist xs ∧ l.length = k := by
  intro xs
  induction xs with
  | nil =>
    intro k l
    cases k with
    | zero => simp [combos, List.sublist_nil]
    | succ k =>
      simp only [combos, List.not_mem_nil, false_iff, not_and]
      intro h
      rw [List.sublist_nil.1 h]; simp
  | cons x xs ih =>
    intro k l
    cases k with
    | zero =>
      simp only [combos, List.mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl; exact ⟨List.nil_sublist _, rfl⟩
      · rintro ⟨_, rfl⟩; rfl
    | succ k =>
      simp only [combos, List.mem_append, List.mem_map, ih]
      constructor
      · rintro (⟨l', ⟨hs, hl⟩, rfl⟩ | ⟨hs, hl⟩)
        · exact ⟨List.Sublist.cons_cons x hs, by simp [hl]⟩
        · exact ⟨List.Sublist.cons x hs, hl⟩
      · rintro ⟨hs, hl⟩
        rcases List.sublist_cons_iff.1 hs with h | ⟨r, rfl, hr⟩
        · right; exact ⟨h, hl⟩
        · left; exact ⟨r, ⟨hr, by simpa using hl⟩, rfl⟩

theorem picks_perm : ∀ (xs : List Nat) (y : Nat) (ys : List Nat),
    (y, ys) ∈ picks xs → (y :: ys).Perm xs := by
  intro xs
  induction xs with
  | nil => intro y ys h; simp [picks] at h
  | cons x xs ih =>
    intro y ys h
    simp only [picks, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨p, hm, hp⟩
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact List.Perm.refl _
    · obtain ⟨y', ys'⟩ := p
      simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact (List.Perm.swap x y' ys').trans ((ih y' ys' hm).cons x)

theorem picks_map_fst : ∀ (xs : List Nat), (picks xs).map Prod.fst = xs := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [picks, List.map_cons, List.map_map]
    congr 1
    first
    | done
    | (rw [← ih]; apply List.map_congr_left; intro p _; cases p; rfl)

theorem picks_mem_erase : ∀ (xs : List Nat) (y : Nat), y ∈ xs → (y, xs.erase y) ∈ picks xs := by
  intro xs
  induction xs with
  | nil => intro y h; exact absurd h List.not_mem_nil
  | cons x xs ih =>
    intro y hy
    simp only [picks, List.mem_cons, List.mem_map]
    by_cases hxy : x = y
    · subst hxy; left; simp
    · right
      have hy' : y ∈ xs := by
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h.symm hxy
        · exact h
      refine ⟨(y, xs.erase y), ih y hy', ?_⟩
      show (y, x :: xs.erase y) = (y, (x :: xs).erase y)
      rw [List.erase_cons_tail (by simpa using hxy)]

theorem picks_length_eq {xs : List Nat} {y : Nat} {ys : List Nat} (h : (y, ys) ∈ picks xs) :
    ys.length + 1 = xs.length := by
  have := (picks_perm xs y ys h).length_eq
  simpa using this

theorem mem_permsAux : ∀ (n : Nat) (xs : List Nat), xs.length = n → xs.Nodup →
    ∀ (l : List Nat), l ∈ permsAux n xs ↔ l.Perm xs := by
  intro n
  induction n with
  | zero =>
    intro xs hlen _ l
    have hxs : xs = [] := List.length_eq_zero_iff.1 hlen
    subst hxs
    simp [permsAux, List.perm_nil]
  | succ n ih =>
    intro xs hlen hnd l
    simp only [permsAux, List.mem_flatMap, List.mem_map, Prod.exists]
    constructor
    · rintro ⟨y, ys, hp, l', hl', rfl⟩
      have hperm := picks_perm xs y ys hp
      have hys_len : ys.length = n := by have := picks_length_eq hp; omega
      have hys_nd : ys.Nodup := (List.nodup_cons.1 (hperm.nodup_iff.2 hnd)).2
      have := (ih ys hys_len hys_nd l').1 hl'
      exact (this.cons y).trans hperm
    · intro hl
      cases l with
      | nil => have := hl.length_eq; simp at this; omega
      | cons y l' =>
        have hy : y ∈ xs := hl.subset List.mem_cons_self
        refine ⟨y, xs.erase y, picks_mem_erase xs y hy, l', ?_, rfl⟩
        have hlen' : (xs.erase y).length = n := by
          rw [List.length_erase_of_mem hy]; omega
        have hnd' : (xs.erase y).Nodup := hnd.erase y
        rw [ih _ hlen' hnd']
        exact (List.cons_perm_iff_perm_erase.1 hl).2

theorem mem_permsOf {xs : List Nat} (hnd : xs.Nodup) {l : List Nat} :
    l ∈ permsOf xs ↔ l.Perm xs :=
  mem_permsAux xs.length xs rfl hnd l

theorem picks_nodup {xs : List Nat} (hnd : xs.Nodup) : (picks xs).Nodup := by
  have : ((picks xs).map Prod.fst).Nodup := by rw [picks_map_fst]; exact hnd
  exact this.of_map _

theorem permsAux_nodup : ∀ (n : Nat) (xs : List Nat), xs.length = n → xs.Nodup →
    (permsAux n xs).Nodup := by
  intro n
  induction n with
  | zero => intro xs _ _; simp [permsAux]
  | succ n ih =>
    intro xs hlen hnd
    simp only [permsAux]
    rw [List.nodup_flatMap]
    constructor
    · rintro ⟨y, ys⟩ hp
      have hperm := picks_perm xs y ys hp
      have hys_len : ys.length = n := by have := picks_length_eq hp; omega
      have hys_nd : ys.Nodup := (List.nodup_cons.1 (hperm.nodup_iff.2 hnd)).2
      exact List.Nodup.map List.cons_injective (ih ys hys_len hys_nd)
    · have hfst : ((picks xs).map Prod.fst).Nodup := by rw [picks_map_fst]; exact hnd
      have hpw : (picks xs).Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.1 hfst
      refine hpw.imp ?_
      rintro ⟨y, ys⟩ ⟨y', ys'⟩ hne
      simp only at hne
      unfold Function.onFun
      rw [List.disjoint_left]
      intro l hl hl'
      obtain ⟨l1, _, rfl⟩ := List.mem_map.1 hl
      obtain ⟨l2, _, heq⟩ := List.mem_map.1 hl'
      exact hne (List.cons.inj heq).1.symm

theorem permsOf_nodup {xs : List Nat} (hnd : xs.Nodup) : (permsOf xs).Nodup :=
  permsAux_nodup xs.length xs rfl hnd

/-- Every min-first step is an entry of the campaign's shape table. -/
theorem minFirst_mem_cyclicShapes {st : List Nat} (hst : WFStep st) :
    minFirst st ∈ cyclicShapes 6 := by
  have hcons : ∀ (l : List Nat), l ≠ [] → l = l.headD 0 :: l.tail := by
    intro l hl
    cases l with
    | nil => exact absurd rfl hl
    | cons a t => rfl
  obtain ⟨s, hs⟩ : ∃ s, s = minFirst st := ⟨_, rfl⟩
  rw [← hs]
  have hsWF : WFStep s := by rw [hs]; exact minFirst_WFStep hst
  obtain ⟨h2, hnd, hlt⟩ := hsWF
  obtain ⟨men, hmen⟩ : ∃ men, men = (List.range 6).filter (fun x => decide (x ∈ s)) := ⟨_, rfl⟩
  have hmen_sub : men.Sublist (List.range 6) := by rw [hmen]; exact List.filter_sublist
  have hmen_nd : men.Nodup := by rw [hmen]; exact List.nodup_range.filter _
  have hmen_perm : men.Perm s := by
    rw [List.perm_ext_iff_of_nodup hmen_nd hnd]
    intro x
    simp only [hmen, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩
  have hmen_len : men.length = s.length := hmen_perm.length_eq
  have hmen_le : men.length ≤ 6 := by
    have := hmen_sub.length_le; simpa using this
  have hs_ne : s ≠ [] := by intro h; rw [h] at h2; simp at h2
  have hmen_ne : men ≠ [] := by
    intro h; have := hmen_len; rw [h, List.length_nil] at this; omega
  -- the head of `men` is the minimum of `st`
  have hmin_s : st.foldl min 6 ∈ s := by rw [hs]; exact mem_rotateTo.2 (stepMin_mem hst)
  have hm0 : st.foldl min 6 ∈ men := hmen_perm.mem_iff.2 hmin_s
  have hsorted : men.Pairwise (· < ·) := by rw [hmen]; exact (List.pairwise_lt_range).filter _
  have hhead : men.headD 0 = st.foldl min 6 := by
    have hmc := hcons men hmen_ne
    rw [hmc] at hm0 hsorted
    rcases List.mem_cons.1 hm0 with h | h
    · exact h.symm
    · have h1 := (List.pairwise_cons.1 hsorted).1 _ h
      have hh0s : men.headD 0 ∈ s := hmen_perm.subset (by rw [hmc]; exact List.mem_cons_self)
      have hh0st : men.headD 0 ∈ st := by rw [hs] at hh0s; exact mem_rotateTo.1 hh0s
      have h2' := foldl_min_le (l := st) 6 _ hh0st
      omega
  have hshead : s.headD 0 = st.foldl min 6 := by rw [hs]; exact minFirst_head hst
  -- assemble the membership
  unfold cyclicShapes
  rw [List.mem_flatMap]
  refine ⟨men.length - 2, ?_, ?_⟩
  · simp only [List.mem_range]; omega
  · rw [List.mem_flatMap]
    refine ⟨men, ?_, ?_⟩
    · rw [mem_combos]; exact ⟨hmen_sub, by omega⟩
    · rw [List.mem_map]
      refine ⟨s.tail, ?_, ?_⟩
      · have hnd_tail : men.tail.Nodup := hmen_nd.tail
        rw [mem_permsOf hnd_tail]
        have h1 : (men.headD 0 :: men.tail).Perm (s.headD 0 :: s.tail) := by
          rw [← hcons men hmen_ne, ← hcons s hs_ne]; exact hmen_perm
        rw [hhead, hshead] at h1
        exact h1.cons_inv.symm
      · show men.headD 0 :: s.tail = s
        rw [hhead, ← hshead]; exact (hcons s hs_ne).symm

/-! ### `permsN 6` -/

theorem mem_permsN6 {mu : List Nat} : mu ∈ permsN 6 ↔ mu.Perm idRow6 := by
  unfold permsN
  rw [mem_permsOf List.nodup_range, idRow6_eq_range]

theorem permsN6_nodup : (permsN 6).Nodup := permsOf_nodup List.nodup_range

theorem permsN6_perm_permutations : (permsN 6).Perm idRow6.permutations := by
  rw [List.perm_ext_iff_of_nodup permsN6_nodup (List.nodup_permutations _ (by decide))]
  intro mu
  rw [mem_permsN6, List.mem_permutations]
