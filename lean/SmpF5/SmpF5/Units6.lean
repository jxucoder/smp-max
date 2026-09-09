import SmpF5.ReadoffSem6
import SmpF5.Cubes6

/-!
# Cube unit clauses are satisfied by the witness assignment (plan §6, items 13–14)

Implements `docs/history/f6-FAITHFULNESS_PLAN.md` §6 items 13 (`prefixUnits_sat`) and
14 (`stopUnits_sat`) on top of the cube side conditions `Cubes6.CubeWF` /
`Cubes6.Fits` of §3.5, and packages the three pieces of a cube formula
(`Cubes6.cubeFormula k c = schedCNFn 6 k ++ prefixUnits 6 c.steps ++
stopUnits 6 c.steps c.stopped`) into `cubeFormula_sat_of` for the assembly
(§7).

* `prefixUnits_sat`: unit `t` of `prefixUnits 6 c.steps` is
  `pos (sVar (layout 6) t ((cyclicShapes 6).idxOf (c.steps.getD t []) + 1))`;
  by `Fits`, `c.steps.getD t [] = minFirst (S.getD t [])` and
  `t < c.steps.length ≤ S.length ≤ 15`, so the index is exactly `stepIdx S t`,
  the id decodes (`dec_sVar`) to `.St t (stepIdx S t)`, and `τV` evaluates it
  to `decide (stepIdx S t = stepIdx S t) = true`.
* `stopUnits_sat`: for a stopped cube, `t := c.steps.length = S.length < 15`
  (`CubeWF`), the unit is `pos (sVar (layout 6) t 0)`, and `stepIdx S t = 0`
  because `¬ t < S.length`.
* `cubeFormula_sat_of`: `List.all_append` twice.

No deviations from the plan statements.
-/

open SchedCNF6

namespace Units6

/-- `getD` of the min-first image of a prefix: for `t` inside the prefix and
inside `S`, it is the min-first form of step `t` of `S`. -/
theorem getD_map_minFirst_take {S : List (List Nat)} {n t : Nat} (htn : t < n)
    (htS : t < S.length) :
    ((S.take n).map minFirst).getD t [] = minFirst (S.getD t []) := by
  have h1 : t < ((S.take n).map minFirst).length := by
    rw [List.length_map, List.length_take]; omega
  rw [List.getD_eq_getElem _ _ h1, List.getElem_map, List.getElem_take,
    List.getD_eq_getElem _ _ htS]

/-- A positive `sVar` unit at frame `t < 15` with index `j ≤ 409` evaluates,
under `tau6`, to `decide (j = stepIdx S t)`. -/
theorem evalClause_sVar_unit (k : Nat) (S : List (List Nat)) (idxs : List Nat)
    {t j : Nat} (ht : t < 15) (hj : j ≤ 409) :
    evalClause (tau6 k S idxs) [pos (sVar (layout 6) t j)] = decide (j = stepIdx S t) := by
  have hpos : 0 < sVar (layout 6) t j := by rw [sVar6]; omega
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false]
  rw [evalLit_pos6 _ hpos]
  unfold tau6
  rw [dec_sVar ht hj]
  rfl

end Units6

set_option linter.unusedVariables false in
/-- Plan §6 item 13: the prefix units of a cube fitting `S` are satisfied.
(`hc` is part of the plan's statement; the shape-alphabet side of `CubeWF`
is not needed because `Fits` already pins every prefix step to a min-first
step of `S`, whose index is bounded by `stepIdx_le`.) -/
theorem prefixUnits_sat {k : Nat} {S : List (List Nat)} {idxs : List Nat} {c : Cubes6.Cube}
    (hWF : ∀ st ∈ S, WFStep st) (hlen : S.length ≤ 15)
    (hc : Cubes6.CubeWF c) (hf : Cubes6.Fits c S) :
    (prefixUnits 6 c.steps).all (evalClause (tau6 k S idxs)) = true := by
  obtain ⟨hsteps, hle, _⟩ := hf
  rw [List.all_eq_true]
  intro cl hcl
  simp only [prefixUnits, List.mem_map, List.mem_range] at hcl
  obtain ⟨t, ht, rfl⟩ := hcl
  have htS : t < S.length := lt_of_lt_of_le ht hle
  have ht15 : t < 15 := lt_of_lt_of_le htS hlen
  have hstep : c.steps.getD t [] = minFirst (S.getD t []) := by
    conv_lhs => rw [hsteps]
    exact Units6.getD_map_minFirst_take ht htS
  have hidx : (cyclicShapes 6).idxOf (c.steps.getD t []) + 1 = stepIdx S t := by
    rw [hstep]; unfold stepIdx; rw [if_pos htS]
  rw [hidx, Units6.evalClause_sVar_unit k S idxs ht15 (stepIdx_le hWF t)]
  simp

set_option linter.unusedVariables false in
/-- Plan §6 item 14: the stop unit of a stopped cube fitting `S` is satisfied.
(`hlen` is part of the plan's statement; `CubeWF` already gives
`c.steps.length < 15` for a stopped cube, which is all `dec_sVar` needs.) -/
theorem stopUnits_sat {k : Nat} {S : List (List Nat)} {idxs : List Nat} {c : Cubes6.Cube}
    (hlen : S.length ≤ 15) (hc : Cubes6.CubeWF c) (hf : Cubes6.Fits c S) :
    (Cubes6.stopUnits 6 c.steps c.stopped).all (evalClause (tau6 k S idxs)) = true := by
  obtain ⟨_, hlt, _⟩ := hc
  obtain ⟨_, _, hstop⟩ := hf
  unfold Cubes6.stopUnits
  split
  · next hst =>
    have hS : S.length = c.steps.length := hstop hst
    have ht15 : c.steps.length < 15 := hlt hst
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [Units6.evalClause_sVar_unit k S idxs ht15 (Nat.zero_le _)]
    unfold stepIdx
    rw [if_neg (by omega)]
    simp
  · rfl

/-- Plan §7: the cube formula is the base formula followed by the prefix and
stop units; it is satisfied as soon as each piece is. -/
theorem cubeFormula_sat_of {k : Nat} {c : Cubes6.Cube} {τ : Nat → Bool}
    (hbase : (schedCNFn 6 k).all (evalClause τ) = true)
    (hpre : (prefixUnits 6 c.steps).all (evalClause τ) = true)
    (hstop : (Cubes6.stopUnits 6 c.steps c.stopped).all (evalClause τ) = true) :
    evalCNF τ (Cubes6.cubeFormula k c) = true := by
  unfold Cubes6.cubeFormula Cubes6.cubeCNFc evalCNF
  rw [List.all_append, List.all_append, hbase, hpre, hstop]
  rfl
