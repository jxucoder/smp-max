import SmpMax.Six.FrameAssignment

/-!
# The frame bound (plan §2)

A legal order-6 schedule has at most 15 steps: every step moves at least
two men, every man moves at most five times (his trajectory is a
duplicate-free list of six possible partners), and the moves are
double-counted by steps and by men.  Also the per-man cap and the
30-move budget that `cube_campaign.apply_step` checks.
-/

/-- L2.1: every listed man really moves. -/
theorem applyStep_moves {st mu : List Nat} (hst : WFStep st) (hmu : mu.Perm idRow6)
    {m : Nat} (hm : m ∈ st) : (applyStep st mu).getD m 0 ≠ mu.getD m 0 := by
  obtain ⟨h2, hnd, hlt⟩ := hst
  have hm6 : m < 6 := hlt m hm
  rw [applyStep_getD hm6, if_pos hm]
  intro heq
  have hsucc6 : st.getD ((idxOf m st + 1) % st.length) 0 < 6 :=
    hlt _ (step_succ_mem h2 hm)
  have := perm6_getD_inj hmu hsucc6 hm6 heq
  -- the successor position differs from `m`'s own position
  have hi : idxOf m st < st.length := idxOf_lt_length hm
  have hpos : (idxOf m st + 1) % st.length < st.length := Nat.mod_lt _ (by omega)
  have h1 : idxOf (st.getD ((idxOf m st + 1) % st.length) 0) st = (idxOf m st + 1) % st.length :=
    idxOf_getD hnd hpos
  rw [this] at h1
  have hne : (idxOf m st + 1) % st.length ≠ idxOf m st := by
    intro h
    rcases Nat.lt_or_ge (idxOf m st + 1) st.length with hlt' | hge
    · rw [Nat.mod_eq_of_lt hlt'] at h; omega
    · have : idxOf m st + 1 = st.length := by omega
      rw [this, Nat.mod_self] at h; omega
  exact hne h1.symm

/-- Number of steps in which `m` participates. -/
def movesOf (S : List (List Nat)) (m : Nat) : Nat :=
  (S.filter (fun st => decide (m ∈ st))).length

theorem movesOf_cons (st : List Nat) (S : List (List Nat)) (m : Nat) :
    movesOf (st :: S) m = (if m ∈ st then 1 else 0) + movesOf S m := by
  unfold movesOf
  rw [List.filter_cons]
  split <;> simp_all <;> omega

/-- L2.2 + L2.3 combined: the trajectory from any start has one more
element than the man has moves. -/
theorem traj_length_from : ∀ (S : List (List Nat)) (start : List Nat), start.Perm idRow6 →
    (∀ st ∈ S, WFStep st) → ∀ (m : Nat), m < 6 →
    (((S.scanl (fun mu st => applyStep st mu) start).map (fun mu => mu.getD m 0)).destutter
        (· ≠ ·)).length = movesOf S m + 1 := by
  intro S
  induction S with
  | nil =>
    intro start _ _ m _
    simp [List.scanl_nil, movesOf]
  | cons st rest ih =>
    intro start hstart hWF m hm
    have hst := hWF st List.mem_cons_self
    have hWF' : ∀ s ∈ rest, WFStep s := fun s hs => hWF s (List.mem_cons_of_mem _ hs)
    have hnext : (applyStep st start).Perm idRow6 := applyStep_perm hst hstart
    have key := ih (applyStep st start) hnext hWF' m hm
    rw [List.scanl_cons, List.map_cons]
    -- the second element of the column
    have hcons : ∃ l, (rest.scanl (fun mu st => applyStep st mu) (applyStep st start)).map
        (fun mu => mu.getD m 0) = (applyStep st start).getD m 0 :: l := by
      cases rest with
      | nil => exact ⟨[], by rw [List.scanl_nil, List.map_cons, List.map_nil]⟩
      | cons s rest' => exact ⟨_, by rw [List.scanl_cons, List.map_cons]⟩
    obtain ⟨l, hbl⟩ := hcons
    rw [hbl] at key ⊢
    rw [List.destutter_cons'] at key ⊢
    rw [movesOf_cons]
    by_cases hmst : m ∈ st
    · have hne : start.getD m 0 ≠ (applyStep st start).getD m 0 :=
        (applyStep_moves hst hstart hmst).symm
      rw [List.destutter'_cons_pos (l := l) hne, List.length_cons, key, if_pos hmst]
      omega
    · have heq : start.getD m 0 = (applyStep st start).getD m 0 := by
        rw [applyStep_getD hm, if_neg hmst]
      rw [List.destutter'_cons_neg (l := l) (by simpa using heq), heq, key, if_neg hmst]
      omega

theorem strajM_length {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) {m : Nat} (hm : m < 6) :
    (strajM S m).length = movesOf S m + 1 :=
  traj_length_from S idRow6 (List.Perm.refl _) hWF m hm

/-- L2.5: a trajectory has at most six entries. -/
theorem strajM_length_le_6 {S : List (List Nat)} (hL : Legal S) {m : Nat} (hm : m < 6) :
    (strajM S m).length ≤ 6 := by
  have hnd := hL.2.1 m hm
  have hsub : strajM S m ⊆ List.range 6 := by
    intro x hx
    rw [List.mem_range]
    exact strajM_all_lt6 hL.1 hm x hx
  have := (hnd.subperm hsub).length_le
  simpa using this

theorem movesOf_le_5 {S : List (List Nat)} (hL : Legal S) {m : Nat} (hm : m < 6) :
    movesOf S m ≤ 5 := by
  have h1 := strajM_length hL.1 hm
  have h2 := strajM_length_le_6 hL hm
  omega

/-! ## Double counting -/

theorem length_filter_eq_sum_ite {p : Nat → Bool} : ∀ (l : List Nat),
    (l.filter p).length = (l.map (fun x => if p x = true then 1 else 0)).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    split
    · next h => simp only [List.length_cons, ih, h]; omega
    · next h => simp only [ih, h]; simp

theorem step_length_eq_count {st : List Nat} (hst : WFStep st) :
    st.length = ((List.range 6).map (fun m => if m ∈ st then 1 else 0)).sum := by
  obtain ⟨_, hnd, hlt⟩ := hst
  have hperm : ((List.range 6).filter (fun m => decide (m ∈ st))).Perm st := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hnd]
    intro x
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩
  rw [← hperm.length_eq, length_filter_eq_sum_ite]
  congr 1
  apply List.map_congr_left
  intro m _
  simp

theorem list_sum_map_add (f g : Nat → Nat) : ∀ (l : List Nat),
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem list_sum_le_of_le (n : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x ≤ n) → l.sum ≤ l.length * n := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x xs ih =>
    intro h
    have hx := h x List.mem_cons_self
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]; omega

/-- L2.4: total step size = total moves over the six men. -/
theorem sum_lengths_double_count : ∀ (S : List (List Nat)), (∀ st ∈ S, WFStep st) →
    (S.map List.length).sum = ((List.range 6).map (fun m => movesOf S m)).sum := by
  intro S
  induction S with
  | nil => simp [movesOf]
  | cons st rest ih =>
    intro hWF
    have hst := hWF st List.mem_cons_self
    have ih' := ih (fun s hs => hWF s (List.mem_cons_of_mem _ hs))
    rw [List.map_cons, List.sum_cons, ih', step_length_eq_count hst]
    simp only [movesOf_cons]
    rw [list_sum_map_add]

/-- The campaign's budget check. -/
theorem moves_le_30 {S : List (List Nat)} (hL : Legal S) : (S.map List.length).sum ≤ 30 := by
  rw [sum_lengths_double_count S hL.1]
  have hbound : ∀ x ∈ (List.range 6).map (fun m => movesOf S m), x ≤ 5 := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
    exact movesOf_le_5 hL (by simpa using hm)
  have := list_sum_le_of_le 5 _ hbound
  simpa using this

theorem two_mul_length_le_sum : ∀ (S : List (List Nat)), (∀ st ∈ S, WFStep st) →
    2 * S.length ≤ (S.map List.length).sum := by
  intro S
  induction S with
  | nil => simp
  | cons st rest ih =>
    intro hWF
    have h2 := (hWF st List.mem_cons_self).1
    have := ih (fun s hs => hWF s (List.mem_cons_of_mem _ hs))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- L2.6: the frame bound. -/
theorem Legal_length_le_15 {S : List (List Nat)} (hL : Legal S) : S.length ≤ 15 := by
  have := two_mul_length_le_sum S hL.1
  have := moves_le_30 hL
  omega
