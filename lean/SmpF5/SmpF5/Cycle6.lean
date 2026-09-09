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

/-! ## Orbit coincidence and the generalized step lemma -/

include hpμ hpν in
theorem orbit_iterate_mem {m0 : Nat} (hm0 : m0 < 6) (k : Nat) :
    (prevOwner μ ν)^[k] m0 ∈ orbit μ ν m0 := by
  obtain ⟨hpos, hret, hle, hleast⟩ := retTime_spec hpμ hpν hm0
  have hper : ∀ k, (prevOwner μ ν)^[k] m0
      = (prevOwner μ ν)^[k % retTime μ ν m0] m0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.lt_or_ge k (retTime μ ν m0) with h | h
      · rw [Nat.mod_eq_of_lt h]
      · obtain ⟨d, rfl⟩ : ∃ d, k = d + retTime μ ν m0 :=
          ⟨k - retTime μ ν m0, by omega⟩
        rw [Nat.add_mod_right, Function.iterate_add_apply, hret]
        exact ih d (by omega)
  rw [hper k]
  exact (orbit_mem_iff hpμ hpν hm0).2
    ⟨k % retTime μ ν m0, Nat.mod_lt _ hpos, rfl⟩

include hpμ hpν in
/-- Orbits through intersecting points coincide (as sets). -/
theorem orbit_eq_of_mem {m0 x z : Nat} (hm0 : m0 < 6)
    (hx : x ∈ orbit μ ν m0) :
    z ∈ orbit μ ν x ↔ z ∈ orbit μ ν m0 := by
  obtain ⟨j, hj, rfl⟩ := (orbit_mem_iff hpμ hpν hm0).1 hx
  have hx6 : (prevOwner μ ν)^[j] m0 < 6 :=
    prevOwner_iterate_lt6 hpμ hpν hm0 j
  constructor
  · intro hz
    obtain ⟨i, hi, rfl⟩ := (orbit_mem_iff hpμ hpν hx6).1 hz
    rw [← Function.iterate_add_apply]
    exact orbit_iterate_mem hpμ hpν hm0 (i + j)
  · intro hz
    obtain ⟨i, hi, rfl⟩ := (orbit_mem_iff hpμ hpν hm0).1 hz
    obtain ⟨hpos, hret, _, _⟩ := retTime_spec hpμ hpν hm0
    have hbase : (prevOwner μ ν)^[retTime μ ν m0 - j]
        ((prevOwner μ ν)^[j] m0) = m0 := by
      rw [← Function.iterate_add_apply,
        show retTime μ ν m0 - j + j = retTime μ ν m0 by omega]
      exact hret
    have hmem := orbit_iterate_mem hpμ hpν hx6
      (i + (retTime μ ν m0 - j))
    rw [Function.iterate_add_apply, hbase] at hmem
    exact hmem

theorem applyStep_getD_notMem {st μ' : List Nat} {x : Nat} (hx6 : x < 6)
    (hx : x ∉ st) : (applyStep st μ').getD x 0 = μ'.getD x 0 := by
  rw [applyStep_getD hx6, if_neg hx]

include hpμ hpν in
/-- Generalized step lemma: the orbit realizes the `μ → ν` move from
any matching that agrees with `μ` on the orbit. -/
theorem applyStep_orbit_moved' {μ' : List Nat} {m0 x : Nat}
    (hm0 : m0 < 6)
    (hagree : ∀ y ∈ orbit μ ν m0, μ'.getD y 0 = μ.getD y 0)
    (hx : x ∈ orbit μ ν m0) (hx6 : x < 6) :
    (applyStep (orbit μ ν m0) μ').getD x 0 = ν.getD x 0 := by
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
  rw [hagree _ (orbit_iterate_mem hpμ hpν hm0 (i + 1))]
  rw [Function.iterate_succ_apply']
  exact prevOwner_getD hpμ hpν (prevOwner_iterate_lt6 hpμ hpν hm0 i)


include hpμ hpν in
theorem orbit_mem_lt6 {m0 x : Nat} (hm0 : m0 < 6)
    (hx : x ∈ orbit μ ν m0) : x < 6 := by
  obtain ⟨i, _, rfl⟩ := (orbit_mem_iff hpμ hpν hm0).1 hx
  exact prevOwner_iterate_lt6 hpμ hpν hm0 i

end

/-! ## Decomposing a full step into disjoint orbits -/

noncomputable def stepDecompAux (μ ν : List Nat) :
    List Nat → List (List Nat) → List (List Nat)
  | [], acc => acc
  | m :: rest, acc =>
    if μ.getD m 0 ≠ ν.getD m 0 ∧ m ∉ acc.flatten
    then stepDecompAux μ ν rest (acc ++ [orbit μ ν m])
    else stepDecompAux μ ν rest acc

noncomputable def stepDecomp (μ ν : List Nat) : List (List Nat) :=
  stepDecompAux μ ν idRow6 []

/-- Invariant: a list of pairwise-disjoint orbits of moved men. -/
def OrbAcc (μ ν : List Nat) (acc : List (List Nat)) : Prop :=
  (∀ st ∈ acc, ∃ m0, m0 < 6 ∧ moved μ ν m0 ∧ st = orbit μ ν m0) ∧
  List.Pairwise (fun s t => ∀ x ∈ s, x ∉ t) acc

section
variable {μ ν : List Nat} (hpμ : μ.Perm idRow6) (hpν : ν.Perm idRow6)

include hpμ hpν in
theorem orbAcc_flatten_lt6 {acc : List (List Nat)} (h : OrbAcc μ ν acc)
    {y : Nat} (hy : y ∈ acc.flatten) : y < 6 := by
  obtain ⟨st, hst, hyst⟩ := List.mem_flatten.1 hy
  obtain ⟨m0, hm06, _, rfl⟩ := h.1 st hst
  exact orbit_mem_lt6 hpμ hpν hm06 hyst

include hpμ hpν in
theorem stepDecompAux_spec :
    ∀ (todo : List Nat) (acc : List (List Nat)),
    (∀ m ∈ todo, m < 6) → OrbAcc μ ν acc →
    OrbAcc μ ν (stepDecompAux μ ν todo acc) ∧
    (∀ y ∈ acc.flatten, y ∈ (stepDecompAux μ ν todo acc).flatten) ∧
    (∀ m ∈ todo, moved μ ν m →
      m ∈ (stepDecompAux μ ν todo acc).flatten) := by
  intro todo
  induction todo with
  | nil =>
    intro acc _ hacc
    refine ⟨hacc, fun y hy => hy, ?_⟩
    intro m hm
    simp at hm
  | cons m rest ih =>
    intro acc htodo hacc
    have hm6 : m < 6 := htodo m List.mem_cons_self
    have hrest : ∀ m' ∈ rest, m' < 6 :=
      fun m' hm' => htodo m' (List.mem_cons_of_mem _ hm')
    simp only [stepDecompAux]
    by_cases hc : μ.getD m 0 ≠ ν.getD m 0 ∧ m ∉ acc.flatten
    · rw [if_pos hc]
      have hmov : moved μ ν m := hc.1
      have hacc' : OrbAcc μ ν (acc ++ [orbit μ ν m]) := by
        constructor
        · intro st hst
          rcases List.mem_append.1 hst with h | h
          · exact hacc.1 st h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            exact ⟨m, hm6, hmov, h⟩
        · rw [List.pairwise_append]
          refine ⟨hacc.2, by simp, ?_⟩
          intro s hs t ht x hxs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          subst ht
          intro hxt
          obtain ⟨m', hm'6, _, rfl⟩ := hacc.1 s hs
          have hx6 : x < 6 := orbit_mem_lt6 hpμ hpν hm'6 hxs
          have h1 : m ∈ orbit μ ν x :=
            (orbit_eq_of_mem hpμ hpν hm6 hxt).2
              (mem_orbit_self hpμ hpν hm6)
          have h2 : m ∈ orbit μ ν m' :=
            (orbit_eq_of_mem hpμ hpν hm'6 hxs).1 h1
          exact hc.2 (List.mem_flatten.2 ⟨orbit μ ν m', hs, h2⟩)
      obtain ⟨h1, h2, h3⟩ := ih (acc ++ [orbit μ ν m]) hrest hacc'
      refine ⟨h1, ?_, ?_⟩
      · intro y hy
        exact h2 y (by
          rw [List.flatten_append]
          exact List.mem_append.2 (Or.inl hy))
      · intro m' hm' hmov'
        rcases List.mem_cons.1 hm' with rfl | hm'r
        · refine h2 m' ?_
          rw [List.flatten_append]
          refine List.mem_append.2 (Or.inr ?_)
          exact List.mem_flatten.2
            ⟨orbit μ ν m', List.mem_cons_self, mem_orbit_self hpμ hpν hm6⟩
        · exact h3 m' hm'r hmov'
    · rw [if_neg hc]
      obtain ⟨h1, h2, h3⟩ := ih acc hrest hacc
      refine ⟨h1, h2, ?_⟩
      intro m' hm' hmov'
      rcases List.mem_cons.1 hm' with rfl | hm'r
      · have : m' ∈ acc.flatten := by
          by_contra hnot
          exact hc ⟨hmov', hnot⟩
        exact h2 m' this
      · exact h3 m' hm'r hmov'

include hpμ hpν in
theorem foldl_orbits :
    ∀ (L : List (List Nat)) (μ' : List Nat), OrbAcc μ ν L →
    (∀ y ∈ L.flatten, μ'.getD y 0 = μ.getD y 0) →
    ∀ x, x < 6 →
    (L.foldl (fun mu st => applyStep st mu) μ').getD x 0 =
      if x ∈ L.flatten then ν.getD x 0 else μ'.getD x 0 := by
  intro L
  induction L with
  | nil =>
    intro μ' _ _ x _
    simp
  | cons O rest ih =>
    intro μ' hOrb hagree x hx
    obtain ⟨horbs, hdisj⟩ := hOrb
    obtain ⟨m0, hm06, hmov, hOdef⟩ := horbs O List.mem_cons_self
    have hOrbRest : OrbAcc μ ν rest :=
      ⟨fun st hst => horbs st (List.mem_cons_of_mem _ hst),
       hdisj.of_cons⟩
    have hdisjO : ∀ z ∈ O, ∀ t ∈ rest, z ∉ t :=
      fun z hz t ht => (List.pairwise_cons.1 hdisj).1 t ht z hz
    rw [List.foldl_cons]
    have hagreeO : ∀ y ∈ orbit μ ν m0, μ'.getD y 0 = μ.getD y 0 := by
      intro y hy
      refine hagree y ?_
      rw [List.flatten_cons]
      exact List.mem_append.2 (Or.inl (hOdef ▸ hy))
    have hagree' : ∀ y ∈ rest.flatten,
        (applyStep O μ').getD y 0 = μ.getD y 0 := by
      intro y hy
      have hy6 : y < 6 := orbAcc_flatten_lt6 hpμ hpν hOrbRest hy
      have hynO : y ∉ O := by
        intro hyO
        obtain ⟨t, ht, hyt⟩ := List.mem_flatten.1 hy
        exact hdisjO y hyO t ht hyt
      rw [applyStep_getD_notMem hy6 hynO]
      refine hagree y ?_
      rw [List.flatten_cons]
      exact List.mem_append.2 (Or.inr hy)
    have hIH := ih (applyStep O μ') hOrbRest hagree' x hx
    rw [hIH]
    rw [List.flatten_cons]
    by_cases hxr : x ∈ rest.flatten
    · rw [if_pos hxr, if_pos (List.mem_append.2 (Or.inr hxr))]
    · rw [if_neg hxr]
      by_cases hxO : x ∈ O
      · rw [if_pos (List.mem_append.2 (Or.inl hxO))]
        subst hOdef
        exact applyStep_orbit_moved' hpμ hpν hm06 hagreeO hxO hx
      · rw [if_neg (by
          intro hc
          rcases List.mem_append.1 hc with h | h
          · exact hxO h
          · exact hxr h)]
        subst hOdef
        exact applyStep_getD_notMem hx hxO

include hpμ hpν in
/-- **Single-step decomposition**: the difference of any two matchings
is realized by a sequence of pairwise-disjoint cyclic steps, each a
well-formed move on moved men. -/
theorem stepDecomp_spec :
    OrbAcc μ ν (stepDecomp μ ν) ∧
    ∀ x, x < 6 →
    ((stepDecomp μ ν).foldl (fun mu st => applyStep st mu) μ).getD x 0
      = ν.getD x 0 := by
  have hbase : OrbAcc μ ν ([] : List (List Nat)) := ⟨by simp, by simp⟩
  have htodo : ∀ m ∈ idRow6, m < 6 := by decide
  obtain ⟨hOrb, hmono, hcov⟩ :=
    stepDecompAux_spec hpμ hpν idRow6 [] htodo hbase
  refine ⟨hOrb, ?_⟩
  intro x hx
  rw [foldl_orbits hpμ hpν (stepDecomp μ ν) μ hOrb (fun y _ => rfl) x hx]
  split
  · rfl
  · next hnot =>
    by_cases hmov : moved μ ν x
    · refine absurd (hcov x ?_ hmov) hnot
      simp only [idRow6, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · exact not_ne_iff.1 hmov

end
