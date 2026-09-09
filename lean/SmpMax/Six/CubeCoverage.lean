import SmpMax.Six.FirstAppearance
import SmpMax.Six.PrefixLegality
import SmpMax.Six.CampaignSplits

/-!
# Coverage of the campaign cubes (plan §3.5, L3.17–L3.20; `docs/history/research-plan-2026-09-08.md` A)

Every legal, first-appearance canonical schedule `S` is covered by a
well-formed cube of the campaign's final cube list:

* `extendCanon_WF`, **L3.19** `canonicalCubes2_WF`, **L3.20**
  `refineCubes_WF`, `finalCubes_WF`: the cube lists consist of well-formed
  cubes (`CubeWF`: at most 15 steps, a stopped cube stops before frame 15,
  every step is a shape of `cyclicShapes 6`).
* `canonNextB_of`: the membership workhorse — the min-first form of step
  `d` of `S` passes the driver's `canonNextB` filter after the min-first
  prefix of length `d` (canonicity via `canonAtB_map_minFirst_take`,
  legality via `Legal_take`, `Legal_map_minFirst`, `legalPrefixB_of_Legal`).
* **L3.17** `cube_of_canonical`: a root cube (`root_cubes(2)`) fits `S`.
* **L3.18** `fits_refine`: fitting is preserved by one round of adaptive
  splitting (`refineCubes`), whatever the split predicate.
* `fits_final`: a cube of `finalCubes` fits `S` and is well-formed — the
  coverage hypothesis of `f6_upper_of_unsat_of_coverage`
  (`Faithfulness6.lean`).

The split predicates `isSplitDepth2`/`isSplitDepth3` of `SplitList6.lean`
are never evaluated: `fits_refine` and `refineCubes_WF` are proved for an
arbitrary `split : Cube → Bool`.

Deviations from the plan statements: none.  The hypothesis `hopen` of
`extendCanon_WF` is kept for the stated interface but is not needed by the
proof (well-formedness of the children only uses `hc` and `hlt`); the
unused-variable linter is silenced locally for that theorem.
-/

open Cubes6 SchedCNF6

namespace Coverage6

/-- Extending the min-first prefix of length `d` by the min-first form of
step `d` gives the min-first prefix of length `d + 1`. -/
theorem take_map_minFirst_succ {S : List (List Nat)} {d : Nat} (hd : d < S.length) :
    (S.take d).map minFirst ++ [minFirst (S.getD d [])] = (S.take (d + 1)).map minFirst := by
  rw [List.getD_eq_getElem _ _ hd, ← List.take_append_getElem hd, List.map_append,
    List.map_singleton]

theorem length_take_map_minFirst {S : List (List Nat)} {d : Nat} (hd : d ≤ S.length) :
    ((S.take d).map minFirst).length = d := by
  rw [List.length_map, List.length_take, Nat.min_eq_left hd]

theorem take_one_map_minFirst {S : List (List Nat)} (h : 0 < S.length) :
    (S.take 1).map minFirst = [minFirst (S.getD 0 [])] := by
  rw [← take_map_minFirst_succ h, List.take_zero, List.map_nil, List.nil_append]

theorem take_two_map_minFirst {S : List (List Nat)} (h : 2 ≤ S.length) :
    (S.take 2).map minFirst = [minFirst (S.getD 0 []), minFirst (S.getD 1 [])] := by
  rw [← take_map_minFirst_succ (by omega : 1 < S.length), take_one_map_minFirst (by omega)]
  rfl

/-- The cube carrying the min-first prefix of length `d` fits `S`, provided
its stop flag is only set when `S` has exactly `d` steps. -/
theorem fits_take {S : List (List Nat)} {d : Nat} (hd : d ≤ S.length) {b : Bool}
    (hb : b = true → S.length = d) : Fits ⟨(S.take d).map minFirst, b⟩ S := by
  have hlen := length_take_map_minFirst hd
  show (S.take d).map minFirst = (S.take ((S.take d).map minFirst).length).map minFirst ∧
    ((S.take d).map minFirst).length ≤ S.length ∧
    (b = true → S.length = ((S.take d).map minFirst).length)
  rw [hlen]
  exact ⟨rfl, hd, hb⟩

/-- The guard of `refineCubes`, unpacked. -/
theorem guard_true {split : Cube → Bool} {c : Cube}
    (hg : (split c && !c.stopped && decide (c.steps.length < 15)) = true) :
    split c = true ∧ c.stopped = false ∧ c.steps.length < 15 := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg
  exact ⟨hg.1.1, hg.1.2, hg.2⟩

end Coverage6

open Coverage6

/-! ## Well-formedness of the cube lists (L3.19, L3.20) -/

set_option linter.unusedVariables false in
/-- The children of an open cube with fewer than 15 steps are well-formed. -/
theorem extendCanon_WF {c : Cube} (hc : CubeWF c) (hopen : c.stopped = false)
    (hlt : c.steps.length < 15) : ∀ c' ∈ extendCanon c, CubeWF c' := by
  intro c' hc'
  unfold extendCanon at hc'
  rcases List.mem_cons.1 hc' with rfl | hc'
  · exact ⟨hc.1, fun _ => hlt, hc.2.2⟩
  · obtain ⟨sh, hsh, rfl⟩ := List.mem_map.1 hc'
    have hsh6 : sh ∈ cyclicShapes 6 := (List.mem_filter.1 hsh).1
    refine ⟨?_, ?_, ?_⟩
    · show (c.steps ++ [sh]).length ≤ 15
      rw [List.length_append, List.length_singleton]
      omega
    · intro h
      exact absurd h (by simp)
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hc.2.2 s hs
      · rw [List.mem_singleton] at hs
        rw [hs]
        exact hsh6

/-- L3.19: the root cubes are well-formed. -/
theorem canonicalCubes2_WF : ∀ c ∈ canonicalCubes2, CubeWF c := by
  intro c hc
  simp only [canonicalCubes2, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_filter] at hc
  rcases hc with (rfl | ⟨s1, ⟨hs1, _⟩, rfl⟩) | ⟨s1, ⟨hs1, _⟩, s2, ⟨hs2, _⟩, rfl⟩
  · exact ⟨by simp, fun _ => by simp, fun sh h => absurd h List.not_mem_nil⟩
  · refine ⟨by simp, fun _ => by simp, fun sh h => ?_⟩
    rw [List.mem_singleton] at h
    rw [h]
    exact hs1
  · refine ⟨by simp, fun h => absurd h (by simp), fun sh h => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact hs1
    · exact hs2

/-- L3.20: one round of adaptive splitting preserves well-formedness, for
any split predicate. -/
theorem refineCubes_WF {cs : List Cube} (h : ∀ c ∈ cs, CubeWF c) (split : Cube → Bool) :
    ∀ c ∈ refineCubes cs split, CubeWF c := by
  intro c hc
  unfold refineCubes at hc
  obtain ⟨c0, hc0, hmem⟩ := List.mem_flatMap.1 hc
  have hmem' : c ∈ (if (split c0 && !c0.stopped && decide (c0.steps.length < 15)) = true
      then extendCanon c0 else [c0]) := hmem
  by_cases hg : (split c0 && !c0.stopped && decide (c0.steps.length < 15)) = true
  · rw [if_pos hg] at hmem'
    obtain ⟨_, hopen, hlt⟩ := guard_true hg
    exact extendCanon_WF (h c0 hc0) hopen hlt c hmem'
  · rw [if_neg hg, List.mem_singleton] at hmem'
    rw [hmem']
    exact h c0 hc0

/-- The campaign's final cube list consists of well-formed cubes. -/
theorem finalCubes_WF : ∀ c ∈ finalCubes, CubeWF c :=
  refineCubes_WF (refineCubes_WF canonicalCubes2_WF isSplitDepth2) isSplitDepth3

/-! ## The membership workhorse -/

/-- The min-first form of step `d` of a legal canonical schedule passes the
driver's filter after the min-first prefix of length `d`. -/
theorem canonNextB_of {S : List (List Nat)} (hL : Legal S) (hcan : ∀ t, canonAtB S t = true)
    {d : Nat} (hd : d < S.length) :
    canonNextB ((S.take d).map minFirst) (minFirst (S.getD d [])) = true := by
  unfold canonNextB
  rw [take_map_minFirst_succ hd, length_take_map_minFirst (Nat.le_of_lt hd), Bool.and_eq_true]
  refine ⟨?_, legalPrefixB_of_Legal (Legal_map_minFirst (Legal_take hL (d + 1)))⟩
  rw [canonAtB_map_minFirst_take hL.1 (Nat.lt_succ_self d)]
  exact hcan d

/-! ## L3.17: a root cube fits -/

theorem cube_of_canonical {S : List (List Nat)} (hL : Legal S)
    (hcan : ∀ t, canonAtB S t = true) : ∃ c ∈ canonicalCubes2, Fits c S := by
  by_cases h0 : S.length = 0
  · -- the `stop` cube
    refine ⟨⟨[], true⟩, List.mem_append_left _ List.mem_cons_self, ?_⟩
    have hf := fits_take (S := S) (d := 0) (Nat.zero_le _) (b := true) (fun _ => h0)
    rw [List.take_zero, List.map_nil] at hf
    exact hf
  by_cases h1 : S.length = 1
  · -- the cube `s1;stop`
    have h0lt : 0 < S.length := by omega
    have hs1 : minFirst (S.getD 0 []) ∈ (cyclicShapes 6).filter (canonNextB []) := by
      refine List.mem_filter.2 ⟨minFirst_mem_cyclicShapes (hL.1 _ (FirstApp6.getD_mem_of_lt h0lt)), ?_⟩
      have := canonNextB_of hL hcan h0lt
      rwa [List.take_zero, List.map_nil] at this
    refine ⟨⟨[minFirst (S.getD 0 [])], true⟩, ?_, ?_⟩
    · simp only [canonicalCubes2]
      exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, hs1, rfl⟩))
    · have hf := fits_take (S := S) (d := 1) (by omega) (b := true) (fun _ => h1)
      rw [take_one_map_minFirst h0lt] at hf
      exact hf
  · -- the open cube `s1;s2`
    have h2 : 2 ≤ S.length := by omega
    have h0lt : 0 < S.length := by omega
    have h1lt : 1 < S.length := by omega
    have hs1 : minFirst (S.getD 0 []) ∈ (cyclicShapes 6).filter (canonNextB []) := by
      refine List.mem_filter.2 ⟨minFirst_mem_cyclicShapes (hL.1 _ (FirstApp6.getD_mem_of_lt h0lt)), ?_⟩
      have := canonNextB_of hL hcan h0lt
      rwa [List.take_zero, List.map_nil] at this
    have hs2 : minFirst (S.getD 1 []) ∈
        (cyclicShapes 6).filter (canonNextB [minFirst (S.getD 0 [])]) := by
      refine List.mem_filter.2 ⟨minFirst_mem_cyclicShapes (hL.1 _ (FirstApp6.getD_mem_of_lt h1lt)), ?_⟩
      have := canonNextB_of hL hcan h1lt
      rwa [take_one_map_minFirst h0lt] at this
    refine ⟨⟨[minFirst (S.getD 0 []), minFirst (S.getD 1 [])], false⟩, ?_, ?_⟩
    · simp only [canonicalCubes2]
      exact List.mem_append_right _
        (List.mem_flatMap.2 ⟨_, hs1, List.mem_map.2 ⟨_, hs2, rfl⟩⟩)
    · have hf := fits_take (S := S) (d := 2) h2 (b := false) (fun h => absurd h (by simp))
      rw [take_two_map_minFirst h2] at hf
      exact hf

/-! ## L3.18: adaptive splitting preserves fitting -/

theorem fits_refine {cs : List Cube} {c : Cube} {S : List (List Nat)} (hL : Legal S)
    (hcan : ∀ t, canonAtB S t = true) (hc : c ∈ cs) (hf : Fits c S) (split : Cube → Bool) :
    ∃ c' ∈ refineCubes cs split, Fits c' S := by
  unfold refineCubes
  by_cases hg : (split c && !c.stopped && decide (c.steps.length < 15)) = true
  · obtain ⟨hsteps, hle, hstop⟩ := hf
    by_cases heq : S.length = c.steps.length
    · -- the stop child
      have hmem : (⟨c.steps, true⟩ : Cube) ∈
          (if (split c && !c.stopped && decide (c.steps.length < 15)) = true
            then extendCanon c else [c]) := by
        rw [if_pos hg]
        exact List.mem_cons_self
      exact ⟨⟨c.steps, true⟩, List.mem_flatMap.2 ⟨c, hc, hmem⟩, hsteps, hle, fun _ => heq⟩
    · -- the open child extending by step `c.steps.length` of `S`
      have hd : c.steps.length < S.length := by omega
      have key := canonNextB_of hL hcan hd
      rw [← hsteps] at key
      have hmem : (⟨c.steps ++ [minFirst (S.getD c.steps.length [])], false⟩ : Cube) ∈
          (if (split c && !c.stopped && decide (c.steps.length < 15)) = true
            then extendCanon c else [c]) := by
        rw [if_pos hg]
        exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_filter.2
          ⟨minFirst_mem_cyclicShapes (hL.1 _ (FirstApp6.getD_mem_of_lt hd)), key⟩, rfl⟩)
      refine ⟨_, List.mem_flatMap.2 ⟨c, hc, hmem⟩, ?_⟩
      have hf' := fits_take (S := S) (d := c.steps.length + 1) hd (b := false)
        (fun h => absurd h (by simp))
      rw [← take_map_minFirst_succ hd, ← hsteps] at hf'
      exact hf'
  · -- the cube is kept as is
    have hmem : c ∈ (if (split c && !c.stopped && decide (c.steps.length < 15)) = true
        then extendCanon c else [c]) := by
      rw [if_neg hg]
      exact List.mem_singleton.2 rfl
    exact ⟨c, List.mem_flatMap.2 ⟨c, hc, hmem⟩, hf⟩

/-! ## Coverage by the final cube list -/

/-- Every legal, first-appearance canonical schedule is covered by a
well-formed cube of the campaign's final cube list. -/
theorem fits_final {S : List (List Nat)} (hL : Legal S) (hcan : ∀ t, canonAtB S t = true) :
    ∃ c ∈ finalCubes, Fits c S ∧ CubeWF c := by
  obtain ⟨c0, hc0, hf0⟩ := cube_of_canonical hL hcan
  obtain ⟨c1, hc1, hf1⟩ := fits_refine hL hcan hc0 hf0 isSplitDepth2
  obtain ⟨c2, hc2, hf2⟩ := fits_refine hL hcan hc1 hf1 isSplitDepth3
  exact ⟨c2, hc2, hf2, finalCubes_WF c2 hc2⟩
