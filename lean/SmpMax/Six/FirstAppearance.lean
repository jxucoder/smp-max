import SmpMax.Six.ScheduleRelabeling

/-!
# First-appearance normalization (order 6)

Implements FAITHFULNESS_PLAN.md §3.3 (L3.8–L3.11), §4.2 L4.14 and §3.5
L3.21, on top of the definitions `firstOcc`, `usedBefore`, `newMen`,
`canonAtB` of `Cubes6.lean` (plan §0: `canonAtB` is set-valued in the
step — it filters `List.range 6` — and only counts `usedBefore`).

* `partOrder S = firstOcc (S.flatten ++ idRow6)` lists the men in order of
  first participation (men who never participate come last, in increasing
  order); `sigmaOf S = invMatch (partOrder S)` so that, for `m < 6`,
  `app (sigmaOf S) m = idxOf m (partOrder S)` (`app_sigmaOf`): the new
  label of a man is the position of his first participation.  This is the
  orientation stated in the plan; it follows from `invMatch_getD`.
* L3.8 `firstOcc_append`, `mem_firstOcc`, `firstOcc_nodup`,
  `firstOcc_sublist`, plus `firstOcc_of_nodup`, `firstOcc_map`,
  `firstOcc_perm`.
* L3.9 `partOrder_perm`, `sigmaOf_perm`, `app_sigmaOf`.
* L3.10 `newMen_relabel`, `usedBefore_relabel`.
* L3.11 `firstApp_relabel`: under `sigmaOf S` every step of `S` is
  first-appearance canonical.  Proof: `partOrder S` decomposes as
  `firstOcc (S.take t).flatten ++ (newMen S t ++ R)` (`partOrder_decomp`),
  so the new men of step `t` receive exactly the labels
  `usedBefore S t, …, usedBefore S t + #new - 1`, and a strictly increasing
  sublist of `range 6` is determined by its members
  (`filter_range_eq_range'`).
* L4.14 `canonAtB_map_minFirst` (rotation invariance), L3.21
  `canonAtB_take`, and the combination `canonAtB_map_minFirst_take`.

Deviations from the plan statements: none in content.  The hypothesis
`∀ st ∈ S, WFStep st` of `app_sigmaOf` and of `canonAtB_map_minFirst` is
kept for interface stability but is not needed by the proofs (it is named
`_hWF`); `newMen_relabel`/`usedBefore_relabel` take `σ.Perm idRow6` and
the well-formedness of `S` (injectivity of `app σ` on the men of `S`).
-/

open Cubes6

/-- Men in order of first participation; the non-participating men follow
in increasing order. -/
def partOrder (S : List (List Nat)) : List Nat := firstOcc (S.flatten ++ idRow6)

/-- The relabeling that makes `S` first-appearance canonical:
`app (sigmaOf S) m = idxOf m (partOrder S)`. -/
def sigmaOf (S : List (List Nat)) : List Nat := invMatch (partOrder S)

namespace FirstApp6

/-! ## The fold behind `firstOcc` -/

/-- The step function of `firstOcc`. -/
def focStep (acc : List Nat) (x : Nat) : List Nat := if x ∈ acc then acc else acc ++ [x]

theorem firstOcc_eq (l : List Nat) : firstOcc l = List.foldl focStep [] l := rfl

theorem mem_focStep {x : Nat} {acc : List Nat} {y : Nat} :
    x ∈ focStep acc y ↔ x ∈ acc ∨ x = y := by
  unfold focStep
  split
  · next h =>
    constructor
    · intro hx; exact Or.inl hx
    · rintro (hx | rfl)
      · exact hx
      · exact h
  · simp

theorem foldl_focStep_append (acc1 : List Nat) : ∀ (l acc2 : List Nat),
    List.foldl focStep (acc1 ++ acc2) l
      = acc1 ++ List.foldl focStep acc2 (l.filter (fun x => decide (x ∉ acc1)))
  | [], acc2 => by simp
  | x :: l, acc2 => by
    by_cases h1 : x ∈ acc1
    · have e : focStep (acc1 ++ acc2) x = acc1 ++ acc2 := by
        simp [focStep, h1]
      rw [List.foldl_cons, e, List.filter_cons_of_neg (by simpa using h1)]
      exact foldl_focStep_append acc1 l acc2
    · rw [List.filter_cons_of_pos (by simpa using h1), List.foldl_cons, List.foldl_cons]
      by_cases h2 : x ∈ acc2
      · have e1 : focStep (acc1 ++ acc2) x = acc1 ++ acc2 := by simp [focStep, h2]
        have e2 : focStep acc2 x = acc2 := by simp [focStep, h2]
        rw [e1, e2]
        exact foldl_focStep_append acc1 l acc2
      · have e1 : focStep (acc1 ++ acc2) x = acc1 ++ (acc2 ++ [x]) := by
          simp [focStep, h1, h2]
        have e2 : focStep acc2 x = acc2 ++ [x] := by simp [focStep, h2]
        rw [e1, e2]
        exact foldl_focStep_append acc1 l (acc2 ++ [x])

theorem mem_foldl_focStep (x : Nat) : ∀ (l acc : List Nat),
    x ∈ List.foldl focStep acc l ↔ x ∈ acc ∨ x ∈ l
  | [], acc => by simp
  | y :: l, acc => by
    rw [List.foldl_cons, mem_foldl_focStep x l (focStep acc y), mem_focStep, List.mem_cons]
    tauto

theorem nodup_foldl_focStep : ∀ (l acc : List Nat), acc.Nodup → (List.foldl focStep acc l).Nodup
  | [], _, h => h
  | y :: l, acc, h => by
    rw [List.foldl_cons]
    apply nodup_foldl_focStep l
    unfold focStep
    split
    · exact h
    · next hy =>
      exact (List.nodup_cons.2 ⟨hy, h⟩).perm (List.perm_append_singleton y acc).symm

theorem foldl_focStep_sublist : ∀ (l acc : List Nat), (List.foldl focStep acc l).Sublist (acc ++ l)
  | [], acc => by simp
  | y :: l, acc => by
    rw [List.foldl_cons]
    refine (foldl_focStep_sublist l (focStep acc y)).trans ?_
    unfold focStep
    split
    · exact List.Sublist.append_left (List.sublist_cons_self y l) acc
    · rw [List.append_assoc, List.singleton_append]

theorem foldl_focStep_of_nodup : ∀ (l acc : List Nat), l.Nodup → (∀ x ∈ l, x ∉ acc) →
    List.foldl focStep acc l = acc ++ l
  | [], acc, _, _ => by simp
  | y :: l, acc, hnd, hdisj => by
    rw [List.foldl_cons]
    have hy : y ∉ acc := hdisj y (by simp)
    have e : focStep acc y = acc ++ [y] := by simp [focStep, hy]
    rw [e, foldl_focStep_of_nodup l (acc ++ [y]) (List.nodup_cons.1 hnd).2 ?_]
    · simp
    · intro x hx
      rw [List.mem_append, List.mem_singleton]
      rintro (h | rfl)
      · exact hdisj x (List.mem_cons_of_mem y hx) h
      · exact (List.nodup_cons.1 hnd).1 hx

theorem foldl_focStep_map {f : Nat → Nat} : ∀ (l acc : List Nat),
    (∀ a ∈ acc ++ l, ∀ b ∈ acc ++ l, f a = f b → a = b) →
    List.foldl focStep (acc.map f) (l.map f) = (List.foldl focStep acc l).map f
  | [], _, _ => by simp
  | y :: l, acc, hinj => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hmem : f y ∈ acc.map f ↔ y ∈ acc := by
      constructor
      · intro h
        obtain ⟨a, ha, hfa⟩ := List.mem_map.1 h
        have := hinj a (by simp [ha]) y (by simp) hfa
        exact this ▸ ha
      · intro h; exact List.mem_map.2 ⟨y, h, rfl⟩
    have e : focStep (acc.map f) (f y) = (focStep acc y).map f := by
      unfold focStep
      by_cases hy : y ∈ acc
      · rw [if_pos (hmem.2 hy), if_pos hy]
      · rw [if_neg (fun h => hy (hmem.1 h)), if_neg hy, List.map_append, List.map_singleton]
    rw [e]
    apply foldl_focStep_map l (focStep acc y)
    have hsub : ∀ z ∈ focStep acc y ++ l, z ∈ acc ++ y :: l := by
      intro z hz
      rw [List.mem_append, mem_focStep] at hz
      rw [List.mem_append, List.mem_cons]
      tauto
    intro a ha b hb hab
    exact hinj a (hsub a ha) b (hsub b hb) hab

end FirstApp6

open FirstApp6

/-! ## L3.8: `firstOcc` -/

theorem firstOcc_append (A B : List Nat) :
    firstOcc (A ++ B)
      = firstOcc A ++ firstOcc (B.filter (fun x => decide (x ∉ firstOcc A))) := by
  simp only [firstOcc_eq]
  rw [List.foldl_append]
  have := foldl_focStep_append (List.foldl focStep [] A) B []
  rw [List.append_nil] at this
  exact this

theorem mem_firstOcc {x : Nat} {l : List Nat} : x ∈ firstOcc l ↔ x ∈ l := by
  rw [firstOcc_eq, mem_foldl_focStep]
  simp

theorem firstOcc_nodup {l : List Nat} : (firstOcc l).Nodup := by
  rw [firstOcc_eq]
  exact nodup_foldl_focStep l [] List.nodup_nil

theorem firstOcc_sublist (l : List Nat) : (firstOcc l).Sublist l := by
  rw [firstOcc_eq]
  have := foldl_focStep_sublist l []
  rwa [List.nil_append] at this

theorem firstOcc_of_nodup {l : List Nat} (h : l.Nodup) : firstOcc l = l := by
  rw [firstOcc_eq]
  have := foldl_focStep_of_nodup l [] h (fun x _ => List.not_mem_nil)
  rwa [List.nil_append] at this

theorem firstOcc_map {f : Nat → Nat} {l : List Nat}
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    firstOcc (l.map f) = (firstOcc l).map f := by
  rw [firstOcc_eq, firstOcc_eq]
  have := foldl_focStep_map (f := f) l [] (by simpa using hinj)
  rwa [List.map_nil] at this

theorem firstOcc_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    (firstOcc l₁).Perm (firstOcc l₂) :=
  (List.perm_ext_iff_of_nodup firstOcc_nodup firstOcc_nodup).2 fun a => by
    rw [mem_firstOcc, mem_firstOcc]
    exact h.mem_iff

theorem firstOcc_length_of_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    (firstOcc l₁).length = (firstOcc l₂).length :=
  (firstOcc_perm h).length_eq

/-! ## Small facts about schedules -/

namespace FirstApp6

theorem getD_map_nil {f : List Nat → List Nat} (hf : f [] = []) (l : List (List Nat)) (i : Nat) :
    (l.map f).getD i [] = f (l.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => simp [hf]
  | some st => rfl

theorem getD_mem_or_nil (S : List (List Nat)) (t : Nat) :
    S.getD t [] ∈ S ∨ S.getD t [] = [] := by
  rw [List.getD_eq_getElem?_getD]
  cases h : S[t]? with
  | none => exact Or.inr rfl
  | some st => exact Or.inl (List.mem_of_getElem? h)

theorem getD_mem_of_lt {S : List (List Nat)} {t : Nat} (ht : t < S.length) :
    S.getD t [] ∈ S := by
  rw [List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

theorem mem_flatten_lt6 {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) {x : Nat}
    (hx : x ∈ S.flatten) : x < 6 := by
  obtain ⟨st, hst, hxs⟩ := List.mem_flatten.1 hx
  exact (hWF st hst).2.2 x hxs

theorem mem_take_flatten_lt6 {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) {t x : Nat}
    (hx : x ∈ (S.take t).flatten) : x < 6 := by
  obtain ⟨st, hst, hxs⟩ := List.mem_flatten.1 hx
  exact (hWF st (List.mem_of_mem_take hst)).2.2 x hxs

theorem mem_getD_lt6 {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) {t x : Nat}
    (hx : x ∈ S.getD t []) : x < 6 := by
  rcases getD_mem_or_nil S t with h | h
  · exact (hWF _ h).2.2 x hx
  · rw [h] at hx
    simp at hx

theorem take_flatten_relabel (σ : List Nat) (S : List (List Nat)) (t : Nat) :
    ((relabelSched σ S).take t).flatten = ((S.take t).flatten).map (app σ) := by
  rw [relabelSched, ← List.map_take, List.map_flatten]

/-- A strictly increasing sublist of `range 6` is determined by its members. -/
theorem filter_range_eq_range' {p : Nat → Bool} {u k : Nat} (hle : u + k ≤ 6)
    (h : ∀ x, x < 6 → (p x = true ↔ (u ≤ x ∧ x < u + k))) :
    (List.range 6).filter p = List.range' u k := by
  have h1 : ((List.range 6).filter p).Pairwise (· < ·) := List.pairwise_lt_range.filter p
  have h2 : (List.range' u k).Pairwise (· < ·) := List.pairwise_lt_range' 1
  have hmem : ∀ a, a ∈ (List.range 6).filter p ↔ a ∈ List.range' u k := by
    intro a
    rw [List.mem_filter, List.mem_range, List.mem_range'_1]
    constructor
    · rintro ⟨ha, hp⟩
      exact (h a ha).1 hp
    · rintro ⟨ha1, ha2⟩
      exact ⟨by omega, (h a (by omega)).2 ⟨ha1, ha2⟩⟩
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => absurd hba (Nat.lt_asymm hab)) h1 h2
    ((List.perm_ext_iff_of_nodup (h1.imp Nat.ne_of_lt) (h2.imp Nat.ne_of_lt)).2 hmem)

theorem flatten_map_perm {f : List Nat → List Nat} (hf : ∀ st, (f st).Perm st) :
    ∀ (L : List (List Nat)), ((L.map f).flatten).Perm L.flatten
  | [] => List.Perm.refl _
  | st :: L => by
    rw [List.map_cons, List.flatten_cons, List.flatten_cons]
    exact (hf st).append (flatten_map_perm hf L)

end FirstApp6

/-! ## L3.9: `partOrder` and `sigmaOf` -/

theorem partOrder_perm {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    (partOrder S).Perm idRow6 := by
  have hnd : idRow6.Nodup := by decide
  refine (List.perm_ext_iff_of_nodup firstOcc_nodup hnd).2 fun a => ?_
  show a ∈ firstOcc (S.flatten ++ idRow6) ↔ a ∈ idRow6
  rw [mem_firstOcc, List.mem_append]
  constructor
  · rintro (h | h)
    · have := mem_flatten_lt6 hWF h
      rw [idRow6_eq_range, List.mem_range]
      exact this
    · exact h
  · exact Or.inr

theorem sigmaOf_perm {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    (sigmaOf S).Perm idRow6 :=
  invMatch_perm (partOrder_perm hWF)

/-- New label = position of first participation (orientation of the plan:
`app (sigmaOf S) m = idxOf m (partOrder S)`; from `invMatch_getD`). -/
theorem app_sigmaOf {S : List (List Nat)} (_hWF : ∀ st ∈ S, WFStep st) {m : Nat}
    (hm : m < 6) : app (sigmaOf S) m = idxOf m (partOrder S) := by
  show (invMatch (partOrder S)).getD m 0 = idxOf m (partOrder S)
  exact invMatch_getD hm

/-! ## L3.10: `newMen` and `usedBefore` under a relabeling -/

theorem newMen_relabel {σ : List Nat} (hp : σ.Perm idRow6) {S : List (List Nat)}
    (hWF : ∀ st ∈ S, WFStep st) (t : Nat) :
    newMen (relabelSched σ S) t = (newMen S t).map (app σ) := by
  have h1 : (relabelSched σ S).getD t [] = (S.getD t []).map (app σ) :=
    getD_map_nil (f := fun st => st.map (app σ)) (by simp) S t
  unfold newMen
  rw [h1, take_flatten_relabel, List.filter_map]
  congr 1
  apply List.filter_congr
  intro m hm
  have hm6 : m < 6 := mem_getD_lt6 hWF hm
  simp only [Function.comp_apply]
  rw [decide_eq_decide, not_iff_not]
  constructor
  · intro h
    obtain ⟨a, ha, hfa⟩ := List.mem_map.1 h
    have := app_inj6 hp (mem_take_flatten_lt6 hWF ha) hm6 hfa
    exact this ▸ ha
  · intro h
    exact List.mem_map.2 ⟨m, h, rfl⟩

theorem usedBefore_relabel {σ : List Nat} (hp : σ.Perm idRow6) {S : List (List Nat)}
    (hWF : ∀ st ∈ S, WFStep st) (t : Nat) :
    usedBefore (relabelSched σ S) t = usedBefore S t := by
  unfold usedBefore
  rw [take_flatten_relabel, firstOcc_map, List.length_map]
  intro a ha b hb hab
  exact app_inj6 hp (mem_take_flatten_lt6 hWF ha) (mem_take_flatten_lt6 hWF hb) hab

/-! ## L3.11: `firstApp_relabel` -/

namespace FirstApp6

/-- `partOrder S` starts with the men of the first `t` steps (in first-
participation order), followed by the new men of step `t` (in step order). -/
theorem partOrder_decomp {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) {t : Nat}
    (ht : t < S.length) :
    ∃ R : List Nat, partOrder S = firstOcc (S.take t).flatten ++ (newMen S t ++ R) := by
  have hst : S.getD t [] ∈ S := getD_mem_of_lt ht
  have htake : S.take (t + 1) = S.take t ++ [S.getD t []] := by
    rw [List.getD_eq_getElem _ _ ht, List.take_append_getElem ht]
  have hS : S.flatten ++ idRow6
      = (S.take t).flatten ++ (S.getD t [] ++ ((S.drop (t + 1)).flatten ++ idRow6)) := by
    calc S.flatten ++ idRow6
        = (S.take (t + 1) ++ S.drop (t + 1)).flatten ++ idRow6 := by
          rw [List.take_append_drop]
      _ = (S.take t).flatten ++ (S.getD t [] ++ ((S.drop (t + 1)).flatten ++ idRow6)) := by
          rw [htake]
          simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.append_assoc]
  have hN : (S.getD t []).filter (fun x => decide (x ∉ firstOcc (S.take t).flatten))
      = newMen S t := by
    unfold newMen
    apply List.filter_congr
    intro m _
    rw [decide_eq_decide, mem_firstOcc]
  have hNnd : (newMen S t).Nodup := (hWF _ hst).2.1.filter _
  have key : partOrder S
      = firstOcc (S.take t).flatten ++ (newMen S t ++
          firstOcc ((((S.drop (t + 1)).flatten ++ idRow6).filter
              (fun x => decide (x ∉ firstOcc (S.take t).flatten))).filter
            (fun x => decide (x ∉ newMen S t)))) := by
    rw [partOrder, hS, firstOcc_append, List.filter_append, firstOcc_append, hN,
      firstOcc_of_nodup hNnd]
  exact ⟨_, key⟩

end FirstApp6

theorem firstApp_relabel {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) (t : Nat) :
    canonAtB (relabelSched (sigmaOf S) S) t = true := by
  have hp : (sigmaOf S).Perm idRow6 := sigmaOf_perm hWF
  unfold canonAtB
  rw [decide_eq_true_eq, newMen_relabel hp hWF, usedBefore_relabel hp hWF, List.length_map]
  by_cases ht : t < S.length
  · obtain ⟨R, hR⟩ := partOrder_decomp hWF ht
    have hlen6 : (partOrder S).length = 6 := perm6_length (partOrder_perm hWF)
    have hu : usedBefore S t = (firstOcc (S.take t).flatten).length := rfl
    have hle : usedBefore S t + (newMen S t).length ≤ 6 := by
      rw [hR] at hlen6
      simp only [List.length_append] at hlen6
      rw [hu]
      omega
    have hNnd : (newMen S t).Nodup := (hWF _ (getD_mem_of_lt ht)).2.1.filter _
    have hidx : ∀ m ∈ newMen S t,
        idxOf m (partOrder S) = usedBefore S t + idxOf m (newMen S t) := by
      intro m hm
      have hmF : m ∉ firstOcc (S.take t).flatten := by
        rw [mem_firstOcc]
        have hm' := hm
        simp only [newMen, List.mem_filter, decide_eq_true_eq] at hm'
        exact hm'.2
      rw [hR, idxOf_append_notMem hmF, idxOf_append_mem hm, hu]
    have hm6 : ∀ m ∈ newMen S t, m < 6 := by
      intro m hm
      have hm' := hm
      simp only [newMen, List.mem_filter, decide_eq_true_eq] at hm'
      exact mem_getD_lt6 hWF hm'.1
    apply filter_range_eq_range' hle
    intro x hx
    simp only [decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [app_sigmaOf hWF (hm6 m hm), hidx m hm]
      have := idxOf_lt_length hm
      omega
    · rintro ⟨h1, h2⟩
      have hlt : x - usedBefore S t < (newMen S t).length := by omega
      have hmem : (newMen S t).getD (x - usedBefore S t) 0 ∈ newMen S t := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      refine ⟨(newMen S t).getD (x - usedBefore S t) 0, hmem, ?_⟩
      rw [app_sigmaOf hWF (hm6 _ hmem), hidx _ hmem, idxOf_getD hNnd hlt]
      omega
  · have hnil : newMen S t = [] := by
      unfold newMen
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt ht)]
      rfl
    rw [hnil]
    simp

/-! ## L4.14: rotation invariance -/

theorem newMen_map_minFirst (S : List (List Nat)) (t : Nat) :
    (newMen (S.map minFirst) t).Perm (newMen S t) := by
  have h1 : (S.map minFirst).getD t [] = minFirst (S.getD t []) := getD_map_nil rfl S t
  have h2 : (((S.map minFirst).take t).flatten).Perm (S.take t).flatten := by
    rw [← List.map_take]
    exact flatten_map_perm (fun _ => minFirst_perm) _
  unfold newMen
  rw [h1]
  have h3 : (minFirst (S.getD t [])).filter
        (fun m => decide (m ∉ ((S.map minFirst).take t).flatten))
      = (minFirst (S.getD t [])).filter (fun m => decide (m ∉ (S.take t).flatten)) := by
    apply List.filter_congr
    intro m _
    rw [decide_eq_decide, h2.mem_iff]
  rw [h3]
  exact List.Perm.filter _ minFirst_perm

theorem usedBefore_map_minFirst (S : List (List Nat)) (t : Nat) :
    usedBefore (S.map minFirst) t = usedBefore S t := by
  unfold usedBefore
  rw [← List.map_take]
  exact firstOcc_length_of_perm (flatten_map_perm (fun _ => minFirst_perm) _)

theorem canonAtB_map_minFirst {S : List (List Nat)} (_hWF : ∀ st ∈ S, WFStep st) (t : Nat) :
    canonAtB (S.map minFirst) t = canonAtB S t := by
  have hN := newMen_map_minFirst S t
  have hX : (List.range 6).filter (fun x => decide (x ∈ newMen (S.map minFirst) t))
      = (List.range 6).filter (fun x => decide (x ∈ newMen S t)) := by
    apply List.filter_congr
    intro x _
    rw [decide_eq_decide]
    exact hN.mem_iff
  unfold canonAtB
  rw [hX, usedBefore_map_minFirst, hN.length_eq]

/-! ## L3.21: prefixes -/

theorem canonAtB_take {S : List (List Nat)} {t d : Nat} (h : t < d) :
    canonAtB (S.take d) t = canonAtB S t := by
  have h1 : (S.take d).take t = S.take t := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt h)]
  have h2 : (S.take d).getD t [] = S.getD t [] := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]
  unfold canonAtB newMen usedBefore
  rw [h1, h2]

/-- The combination used by the coverage lemma: canonicity of the
min-first prefix `(S.take d).map minFirst` at `t < d` is canonicity of `S`
at `t`. -/
theorem canonAtB_map_minFirst_take {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st)
    {t d : Nat} (h : t < d) :
    canonAtB ((S.take d).map minFirst) t = canonAtB S t := by
  rw [canonAtB_map_minFirst (fun st hst => hWF st (List.mem_of_mem_take hst)) t,
    canonAtB_take h]

namespace FirstApp6

/-- Well-formed steps stay well-formed under a relabeling by a permutation
(the first component of `Legal_relabel`, proved here so that this file is
self-contained). -/
theorem WFStep_relabelSched {σ : List Nat} (hp : σ.Perm idRow6) {S : List (List Nat)}
    (hWF : ∀ st ∈ S, WFStep st) : ∀ st ∈ relabelSched σ S, WFStep st := by
  intro st hst
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hst
  obtain ⟨h2, hnd, hlt⟩ := hWF s hs
  refine ⟨by simpa using h2, ?_, ?_⟩
  · refine List.Nodup.map_on ?_ hnd
    intro a ha b hb hab
    exact app_inj6 hp (hlt a ha) (hlt b hb) hab
  · intro m hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
    exact app_lt6 hp (hlt a ha)

end FirstApp6

/-- Every step of the `sigmaOf`-relabeled schedule is canonical, also after
truncation and min-first rotation. -/
theorem firstApp_relabel_map_minFirst_take {S : List (List Nat)}
    (hWF : ∀ st ∈ S, WFStep st) {t d : Nat} (h : t < d) :
    canonAtB (((relabelSched (sigmaOf S) S).take d).map minFirst) t = true := by
  rw [canonAtB_map_minFirst_take (WFStep_relabelSched (sigmaOf_perm hWF) hWF) h]
  exact firstApp_relabel hWF t
