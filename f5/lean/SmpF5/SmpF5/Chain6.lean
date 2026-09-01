import SmpF5.Lattice6

/-!
# Maximal chains in the dominance order (L5 prep)

`theChain I` walks from `manOpt I` to `womanOpt I` by repeatedly moving
to the strict dominator of minimum rank-sum. Minimality of the rank-sum
makes every step a cover for free.
-/

def sumRank (I : Inst6) (mu : List Nat) : Nat :=
  ((List.range 6).map fun m => get2 I.mrank m (mu.getD m 0)).sum

/-- Strict dominance, decidably. -/
def strictDomB (I : Inst6) (μ ν : List Nat) : Bool :=
  ((List.range 6).all fun m =>
    decide (get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m (ν.getD m 0))) &&
  !(μ == ν)

theorem strictDomB_iff {I : Inst6} {μ ν : List Nat} :
    strictDomB I μ ν = true ↔ (domLe I μ ν ∧ μ ≠ ν) := by
  simp only [strictDomB, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, domLe]

/-! ## Sum monotonicity -/

theorem map_sum_le {f g : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

theorem map_sum_lt {f g : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, f x ≤ g x) → (∃ x ∈ l, f x < g x) →
    (l.map f).sum < (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons a t ih =>
    intro h ⟨x, hx, hlt⟩
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h2 := map_sum_le fun y hy => h y (List.mem_cons_of_mem _ hy)
      omega
    · have h1 := h a List.mem_cons_self
      have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨x, hx', hlt⟩
      omega

theorem sumRank_le_of_domLe {I : Inst6} {μ ν : List Nat}
    (h : domLe I μ ν) : sumRank I μ ≤ sumRank I ν :=
  map_sum_le fun m hm => h m (by simpa using hm)

/-- Strict dominance strictly increases the rank-sum (uses rank
injectivity to find a strict coordinate). -/
theorem sumRank_lt_of_strict {I : Inst6} (hWF : WF6 I = true)
    {μ ν : List Nat} (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I)
    (hdom : domLe I μ ν) (hne : μ ≠ ν) : sumRank I μ < sumRank I ν := by
  refine map_sum_lt (fun m hm => hdom m (by simpa using hm)) ?_
  by_contra hall
  push_neg at hall
  apply hne
  refine dominance_antisymm hWF hμ hν hdom ?_
  intro m hm
  have := hall m (by simpa using hm)
  omega

/-- Pointwise `≤` with equal sums forces pointwise equality. -/
theorem domLe_eq_of_sum_eq {I : Inst6} (hWF : WF6 I = true)
    {μ ν : List Nat} (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I)
    (hdom : domLe I μ ν) (hsum : sumRank I ν ≤ sumRank I μ) : μ = ν := by
  by_contra hne
  have := sumRank_lt_of_strict hWF hμ hν hdom hne
  omega

/-! ## Argmin by rank-sum -/

def pickMin (I : Inst6) (x : List Nat) (xs : List (List Nat)) : List Nat :=
  xs.foldl (fun acc y => if sumRank I y < sumRank I acc then y else acc) x

theorem pickMin_spec {I : Inst6} :
    ∀ (xs : List (List Nat)) (x : List Nat),
    (pickMin I x xs = x ∨ pickMin I x xs ∈ xs) ∧
    (sumRank I (pickMin I x xs) ≤ sumRank I x) ∧
    (∀ y ∈ xs, sumRank I (pickMin I x xs) ≤ sumRank I y) := by
  intro xs
  induction xs with
  | nil => intro x; exact ⟨Or.inl rfl, le_refl _, by simp⟩
  | cons a t ih =>
    intro x
    have hstep : pickMin I x (a :: t) =
        pickMin I (if sumRank I a < sumRank I x then a else x) t := rfl
    by_cases hc : sumRank I a < sumRank I x
    · rw [hstep, if_pos hc]
      obtain ⟨hmem, hle, hall⟩ := ih a
      refine ⟨?_, by omega, ?_⟩
      · rcases hmem with h | h
        · exact Or.inr (by rw [h]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · omega
        · exact hall y hy'
    · rw [hstep, if_neg hc]
      obtain ⟨hmem, hle, hall⟩ := ih x
      refine ⟨?_, hle, ?_⟩
      · rcases hmem with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · omega
      · exact hall y hy'
