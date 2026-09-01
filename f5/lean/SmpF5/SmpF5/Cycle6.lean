import SmpF5.AbsBridge6
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# Cycle structure of a matching step (orbit return)

For two matchings `μ ν`, iterating `prevOwner μ ν` from a moved man
walks his cycle. Injectivity (`prevOwner_inj`) plus pigeonhole on the
six men forces a return to the start within six steps — the fact that
makes fuel-6 orbit extraction total and correct.
-/

section
variable {μ ν : List Nat}

theorem prevOwner_iterate_lt6 (hpμ : μ.Perm idRow6) (hpν : ν.Perm idRow6)
    {m : Nat} (hm : m < 6) (n : Nat) : (prevOwner μ ν)^[n] m < 6 := by
  induction n generalizing m with
  | zero => simpa using hm
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (prevOwner_lt6 hpμ hpν hm)

theorem prevOwner_iterate_moved (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) {m : Nat} (hm : m < 6) (hmov : moved μ ν m)
    (n : Nat) : moved μ ν ((prevOwner μ ν)^[n] m) := by
  induction n generalizing m with
  | zero => simpa using hmov
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (prevOwner_lt6 hpμ hpν hm) (prevOwner_moved hpμ hpν hm hmov)

theorem prevOwner_iterate_cancel (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) :
    ∀ (i : Nat) {x y : Nat}, x < 6 → y < 6 →
    (prevOwner μ ν)^[i] x = (prevOwner μ ν)^[i] y → x = y := by
  intro i
  induction i with
  | zero => intro x y _ _ h; simpa using h
  | succ k ih =>
    intro x y hx hy h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    have := ih (prevOwner_lt6 hpμ hpν hx) (prevOwner_lt6 hpμ hpν hy) h
    exact prevOwner_inj hpμ hpν hx hy this

/-- **Orbit return**: iterating `prevOwner` from any man returns to the
start within six steps. -/
theorem prevOwner_return (hpμ : μ.Perm idRow6) (hpν : ν.Perm idRow6)
    {m : Nat} (hm : m < 6) :
    ∃ r, 0 < r ∧ r ≤ 6 ∧ (prevOwner μ ν)^[r] m = m := by
  have hmaps : ∀ i ∈ Finset.range 7,
      (prevOwner μ ν)^[i] m ∈ Finset.range 6 := by
    intro i _
    rw [Finset.mem_range]
    exact prevOwner_iterate_lt6 hpμ hpν hm i
  have hcard : (Finset.range 6).card < (Finset.range 7).card := by simp
  obtain ⟨a, ha, b, hb, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at ha hb
  rcases Nat.lt_or_ge a b with hab | hab
  · obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
    rw [Function.iterate_add_apply] at heq
    have := prevOwner_iterate_cancel hpμ hpν a hm
      (prevOwner_iterate_lt6 hpμ hpν hm d) heq
    exact ⟨d, by omega, by omega, this.symm⟩
  · have hba : b < a := by omega
    obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
    rw [Function.iterate_add_apply] at heq
    have := prevOwner_iterate_cancel hpμ hpν b
      (prevOwner_iterate_lt6 hpμ hpν hm d) hm heq
    exact ⟨d, by omega, by omega, this⟩

end

/-! ## The orbit list -/

open Classical in
/-- Least positive return time of `prevOwner`-iteration (1 if none —
never the case for permutations). -/
noncomputable def retTime (μ ν : List Nat) (m0 : Nat) : Nat :=
  if h : ∃ r, 0 < r ∧ (prevOwner μ ν)^[r] m0 = m0 then Nat.find h else 1

/-- The cycle through `m0`, in `applyStep` order. -/
noncomputable def orbit (μ ν : List Nat) (m0 : Nat) : List Nat :=
  (List.range (retTime μ ν m0)).map (fun i => (prevOwner μ ν)^[i] m0)

section
variable {μ ν : List Nat} (hpμ : μ.Perm idRow6) (hpν : ν.Perm idRow6)

include hpμ hpν in
theorem retTime_exists {m0 : Nat} (hm0 : m0 < 6) :
    ∃ r, 0 < r ∧ (prevOwner μ ν)^[r] m0 = m0 := by
  obtain ⟨r, h1, _, h3⟩ := prevOwner_return hpμ hpν hm0
  exact ⟨r, h1, h3⟩

include hpμ hpν in
theorem retTime_spec {m0 : Nat} (hm0 : m0 < 6) :
    0 < retTime μ ν m0 ∧
    (prevOwner μ ν)^[retTime μ ν m0] m0 = m0 ∧
    retTime μ ν m0 ≤ 6 ∧
    ∀ t, 0 < t → t < retTime μ ν m0 → (prevOwner μ ν)^[t] m0 ≠ m0 := by
  have hex := retTime_exists hpμ hpν hm0
  unfold retTime
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  refine ⟨h1, h2, ?_, ?_⟩
  · obtain ⟨r, hr1, hr2, hr3⟩ := prevOwner_return hpμ hpν hm0
    have := Nat.find_min' hex ⟨hr1, hr3⟩
    omega
  · intro t ht1 ht2
    intro hc
    exact absurd ⟨ht1, hc⟩ (Nat.find_min hex ht2)

theorem getD_range_map {α : Type} {f : Nat → α} {d : α} {n i : Nat}
    (hi : i < n) : (((List.range n).map f).getD i d) = f i := by
  have h1 : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem _ _ h1]
  simp

include hpμ hpν in
theorem orbit_getD {m0 : Nat} (hm0 : m0 < 6) {i : Nat}
    (hi : i < retTime μ ν m0) :
    (orbit μ ν m0).getD i 0 = (prevOwner μ ν)^[i] m0 := by
  unfold orbit
  exact getD_range_map hi

theorem orbit_length {m0 : Nat} : (orbit μ ν m0).length = retTime μ ν m0 := by
  simp [orbit]

include hpμ hpν in
theorem orbit_nodup {m0 : Nat} (hm0 : m0 < 6) : (orbit μ ν m0).Nodup := by
  obtain ⟨hpos, hret, hle, hleast⟩ := retTime_spec hpμ hpν hm0
  unfold orbit
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj heq
  simp only [List.mem_range] at hi hj
  by_contra hne
  rcases Nat.lt_or_ge i j with hij | hij
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    rw [Function.iterate_add_apply] at heq
    have := prevOwner_iterate_cancel hpμ hpν i hm0
      (prevOwner_iterate_lt6 hpμ hpν hm0 d) heq
    exact hleast d (by omega) (by omega) this.symm
  · have hji : j < i := by omega
    obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    rw [Function.iterate_add_apply] at heq
    have := prevOwner_iterate_cancel hpμ hpν j
      (prevOwner_iterate_lt6 hpμ hpν hm0 d) hm0 heq
    exact hleast d (by omega) (by omega) this
    
include hpμ hpν in
theorem orbit_mem_iff {m0 x : Nat} (hm0 : m0 < 6) :
    x ∈ orbit μ ν m0 ↔
    ∃ i, i < retTime μ ν m0 ∧ x = (prevOwner μ ν)^[i] m0 := by
  unfold orbit
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

include hpμ hpν in
theorem orbit_WFStep {m0 : Nat} (hm0 : m0 < 6) (hmov : moved μ ν m0) :
    WFStep (orbit μ ν m0) := by
  obtain ⟨hpos, hret, hle, hleast⟩ := retTime_spec hpμ hpν hm0
  refine ⟨?_, orbit_nodup hpμ hpν hm0, ?_⟩
  · rw [orbit_length]
    by_contra hlt
    have hr1 : retTime μ ν m0 = 1 := by omega
    rw [hr1] at hret
    simp only [Function.iterate_one] at hret
    exact prevOwner_ne hpμ hpν hm0 hmov hret
  · intro x hx
    obtain ⟨i, _, rfl⟩ := (orbit_mem_iff hpμ hpν hm0).1 hx
    exact prevOwner_iterate_lt6 hpμ hpν hm0 i

include hpμ hpν in
theorem orbit_all_moved {m0 : Nat} (hm0 : m0 < 6) (hmov : moved μ ν m0) :
    ∀ x ∈ orbit μ ν m0, moved μ ν x := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := (orbit_mem_iff hpμ hpν hm0).1 hx
  exact prevOwner_iterate_moved hpμ hpν hm0 hmov i

include hpμ hpν in
theorem mem_orbit_self {m0 : Nat} (hm0 : m0 < 6) : m0 ∈ orbit μ ν m0 := by
  obtain ⟨hpos, _, _, _⟩ := retTime_spec hpμ hpν hm0
  exact (orbit_mem_iff hpμ hpν hm0).2 ⟨0, hpos, rfl⟩

include hpμ hpν in
/-- **The orbit realizes the step**: applying the orbit as a cyclic
move sends every orbit member to its `ν`-partner (and fixes everyone
else — `applyStep_orbit_fixed`). -/
theorem applyStep_orbit_moved {m0 x : Nat} (hm0 : m0 < 6)
    (hx : x ∈ orbit μ ν m0) (hx6 : x < 6) :
    (applyStep (orbit μ ν m0) μ).getD x 0 = ν.getD x 0 := by
  obtain ⟨hpos, hret, hle, hleast⟩ := retTime_spec hpμ hpν hm0
  obtain ⟨i, hi, rfl⟩ := (orbit_mem_iff hpμ hpν hm0).1 hx
  rw [applyStep_getD hx6, if_pos hx]
  have hidx : idxOf ((prevOwner μ ν)^[i] m0) (orbit μ ν m0) = i := by
    have h1 : (orbit μ ν m0).getD i 0 = (prevOwner μ ν)^[i] m0 :=
      orbit_getD hpμ hpν hm0 hi
    rw [← h1]
    refine idxOf_getD (orbit_nodup hpμ hpν hm0) ?_
    rw [orbit_length]
    exact hi
  rw [hidx, orbit_length]
  have hnext : (orbit μ ν m0).getD ((i + 1) % retTime μ ν m0) 0
      = (prevOwner μ ν)^[i + 1] m0 := by
    rcases Nat.lt_or_ge (i + 1) (retTime μ ν m0) with h | h
    · rw [Nat.mod_eq_of_lt h]
      exact orbit_getD hpμ hpν hm0 h
    · have heq : i + 1 = retTime μ ν m0 := by omega
      rw [heq, Nat.mod_self]
      rw [orbit_getD hpμ hpν hm0 hpos]
      rw [← heq] at hret ⊢
      rw [hret]
      simp
  rw [hnext]
  rw [Function.iterate_succ_apply']
  exact prevOwner_getD hpμ hpν (prevOwner_iterate_lt6 hpμ hpν hm0 i)

theorem applyStep_orbit_fixed {m0 x : Nat} (hx6 : x < 6)
    (hx : x ∉ orbit μ ν m0) :
    (applyStep (orbit μ ν m0) μ).getD x 0 = μ.getD x 0 := by
  rw [applyStep_getD hx6, if_neg hx]

end
