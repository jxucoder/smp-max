import SmpF5.Symmetry
import SmpF5.ValidityBridge6

/-!
# Position lemmas for destuttered columns (plan §5.1)

A person's trajectory is the destutter (`· ≠ ·`) of their partner column.
The CNF's visited masks read the *column prefix* `col.take (t+1)`; the
read-off ranks read positions in the *trajectory*.  These lemmas connect
the two through `idxOf` (first-occurrence position):

* destutter (≠) keeps every element (`mem_destutter_ne_iff`);
* it preserves the order of first occurrences (`idxOf_destutter_lt_iff`);
* membership in a prefix is a bound on the first occurrence
  (`mem_take_iff_idxOf_lt`);
* positions in a reversed duplicate-free list (`idxOf_reverse_lt_iff`)
  and in a filtered `range` (`idxOf_filter_range_lt`).
-/

/-! ## Membership -/

theorem mem_destutter'_ne_iff : ∀ (l : List Nat) (a x : Nat),
    x ∈ l.destutter' (· ≠ ·) a ↔ x = a ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro a x; simp [List.destutter'_nil]
  | cons b l ih =>
    intro a x
    by_cases hab : a ≠ b
    · rw [List.destutter'_cons_pos (l := l) hab, List.mem_cons, ih]
      simp only [List.mem_cons]
    · rw [List.destutter'_cons_neg (l := l) hab, ih]
      have hab' : a = b := by simpa using hab
      subst hab'
      simp only [List.mem_cons]
      constructor
      · rintro (h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

theorem mem_destutter_ne_iff {l : List Nat} {x : Nat} :
    x ∈ l.destutter (· ≠ ·) ↔ x ∈ l := by
  cases l with
  | nil => simp [List.destutter_nil]
  | cons a l =>
    rw [List.destutter_cons', mem_destutter'_ne_iff]
    simp only [List.mem_cons]

/-! ## Order of first occurrences -/

theorem idxOf_destutter'_lt_iff : ∀ (l : List Nat) (a x y : Nat),
    x ∈ a :: l → y ∈ a :: l →
    (idxOf x (l.destutter' Ne a) < idxOf y (l.destutter' Ne a) ↔
      idxOf x (a :: l) < idxOf y (a :: l)) := by
  intro l
  induction l with
  | nil =>
    intro a x y hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    subst hx; subst hy
    simp [List.destutter'_nil]
  | cons b l ih =>
    intro a x y hx hy
    by_cases hab : a ≠ b
    · rw [List.destutter'_cons_pos (l := l) hab]
      by_cases hax : a = x <;> by_cases hay : a = y
      · simp only [idxOf, if_pos hax, if_pos hay]
      · simp only [idxOf, if_pos hax, if_neg hay]; omega
      · simp only [idxOf, if_neg hax, if_pos hay]; omega
      · have hx' : x ∈ b :: l := by
          rcases List.mem_cons.1 hx with h | h
          · exact absurd h.symm hax
          · exact h
        have hy' : y ∈ b :: l := by
          rcases List.mem_cons.1 hy with h | h
          · exact absurd h.symm hay
          · exact h
        have key := ih b x y hx' hy'
        simp only [idxOf, if_neg hax, if_neg hay]
        simp only [idxOf] at key
        omega
    · have hab' : a = b := by simpa using hab
      subst hab'
      rw [List.destutter'_cons_neg (l := l) hab]
      by_cases hax : a = x <;> by_cases hay : a = y
      · subst hax; subst hay; simp
      · have hy' : y ∈ a :: l := by
          rcases List.mem_cons.1 hy with h | h
          · exact absurd h.symm hay
          · exact h
        have key := ih a x y (by simp [← hax]) hy'
        simp only [idxOf, if_pos hax, if_neg hay] at key ⊢
        omega
      · have hx' : x ∈ a :: l := by
          rcases List.mem_cons.1 hx with h | h
          · exact absurd h.symm hax
          · exact h
        have key := ih a x y hx' (by simp [← hay])
        simp only [idxOf, if_neg hax, if_pos hay] at key ⊢
        omega
      · have hx' : x ∈ a :: l := by
          rcases List.mem_cons.1 hx with h | h
          · exact absurd h.symm hax
          · exact h
        have hy' : y ∈ a :: l := by
          rcases List.mem_cons.1 hy with h | h
          · exact absurd h.symm hay
          · exact h
        have key := ih a x y hx' hy'
        simp only [idxOf, if_neg hax, if_neg hay] at key ⊢
        omega

theorem idxOf_destutter_lt_iff {l : List Nat} {x y : Nat} (hx : x ∈ l) (hy : y ∈ l) :
    idxOf x (l.destutter (· ≠ ·)) < idxOf y (l.destutter (· ≠ ·)) ↔
      idxOf x l < idxOf y l := by
  cases l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a l =>
    rw [List.destutter_cons']
    exact idxOf_destutter'_lt_iff l a x y hx hy

/-! ## Prefix membership -/

theorem mem_take_iff_idxOf_lt : ∀ (l : List Nat) (k x : Nat), x ∈ l →
    (x ∈ l.take k ↔ idxOf x l < k) := by
  intro l
  induction l with
  | nil => intro k x hx; exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    intro k x hx
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.take_succ_cons, List.mem_cons, idxOf]
      by_cases hyx : y = x
      · simp [hyx]
      · rw [if_neg hyx]
        have hx' : x ∈ ys := by
          rcases List.mem_cons.1 hx with h | h
          · exact absurd h.symm hyx
          · exact h
        rw [ih k x hx']
        constructor
        · rintro (h | h)
          · exact absurd h.symm hyx
          · omega
        · intro h; right; omega

/-! ## Reversal -/

theorem idxOf_reverse {l : List Nat} (hnd : l.Nodup) {x : Nat} (hx : x ∈ l) :
    idxOf x l.reverse = l.length - 1 - idxOf x l := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    have hnd' := List.nodup_cons.1 hnd
    rw [List.reverse_cons]
    by_cases hyx : y = x
    · subst hyx
      have hn : y ∉ ys.reverse := fun h => hnd'.1 (List.mem_reverse.1 h)
      rw [idxOf_append_notMem hn]
      simp [idxOf]
    · have hx' : x ∈ ys := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hyx
        · exact h
      have hm : x ∈ ys.reverse := List.mem_reverse.2 hx'
      rw [idxOf_append_mem hm, ih hnd'.2 hx']
      have hlt := idxOf_lt_length hx'
      simp only [idxOf, if_neg hyx, List.length_cons]
      omega

theorem idxOf_reverse_lt_iff {l : List Nat} (hnd : l.Nodup) {x y : Nat}
    (hx : x ∈ l) (hy : y ∈ l) :
    idxOf x l.reverse < idxOf y l.reverse ↔ idxOf y l < idxOf x l := by
  rw [idxOf_reverse hnd hx, idxOf_reverse hnd hy]
  have h1 := idxOf_lt_length hx
  have h2 := idxOf_lt_length hy
  omega

/-! ## Filtered ranges -/

theorem idxOf_filter_range_lt {p : Nat → Bool} {a b : Nat}
    (ha : a ∈ (List.range 6).filter p) (hb : b ∈ (List.range 6).filter p) :
    idxOf a ((List.range 6).filter p) < idxOf b ((List.range 6).filter p) ↔ a < b := by
  have hsorted : ((List.range 6).filter p).Pairwise (fun x y => x < y) :=
    (List.pairwise_lt_range).filter p
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact hab
    · subst hab; exact absurd h (lt_irrefl _)
    · have := idxOf_lt_of_sorted (key := id) _ hsorted hb ha hab
      omega
  · intro hab
    exact idxOf_lt_of_sorted (key := id) _ hsorted ha hb hab
