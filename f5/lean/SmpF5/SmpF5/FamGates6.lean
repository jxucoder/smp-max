import SmpF5.ReadoffSem6

/-!
# Clause families 5–9: the definitional gates (plan §6, items 5–9)

Implements `f6/FAITHFULNESS_PLAN.md` §6, items 5–9, together with the
generic gate lemmas of §6 (the `and2_sat` / `or_sat` pattern, stated
here on the exact `pos`/`neg` literal patterns that occur inside the
`SchedCNF6` definitions):

* `gate_and2`    — `x ↔ y ∧ z`     : `[-x, y], [-x, z], [x, -y, -z]`      (`later`);
* `gate_and_not` — `x ↔ y ∧ ¬z`    : `[-x, y], [-x, -z], [x, -y, z]`      (`C`, `CW`, `only_a`);
* `gate_nor`     — `x ↔ ¬y ∧ ¬z`   : `[-x, -y], [-x, -z], [x, y, z]`      (`neither`, `nv`);
* `gate_eq`      — `x ↔ y`         : `[-y, x], [-x, y]`                  (`PM`, `a > b`);
* `gate_or`      — `x ↔ ⋁ ys`      : `[-y, x]` for `y ∈ ys`, `[-x, ys…]` (`before`, `beforeW`, `PM`, `PW`);
* `gate_or_map`  — `gate_or` for `ys = l.map f` with a pointwise description of `τ ∘ f`.

The family lemmas `before_sat`, `neither_sat`, `pm_sat`, `beforeW_sat`,
`pw_sat` say that the corresponding `SchedCNF6` families at `layout 6`
are satisfied by `tau6 k S idxs` for **every** `k`, `S`, `idxs`: `τV`
(`Frames6.lean`) assigns each derived variable by the very gate formula
the Python encoder emits (`C = V_t[m][a] ∧ ¬V_t[m][b]`, `before = ⋁_t C`,
`PM = before ∨ (a < b ∧ neither)`, …), so no hypothesis on the schedule
is needed.  The `decide (a < b) && …` factor of `τV` is what makes the
`PM` family (no `neither` term for `a > b`) and the `PW` family (the
optional `nv` term) hold in both cases.

Statements are exactly those of the plan (no deviations).  Helper lemmas
(`(layout 6).n = 6`, positivity of the ids, evaluation of `tau6` on each
derived id) live in the namespace `FamGates6` to avoid clashes with the
sibling family files.
-/

open SchedCNF6

/-! ## Generic gate lemmas -/

section Gates

variable (τ : Nat → Bool)

/-- `x ↔ y ∧ z`: clauses `[-x, y], [-x, z], [x, -y, -z]`. -/
theorem gate_and2 {x y z : Nat} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : τ x = (τ y && τ z)) :
    [[neg x, pos y], [neg x, pos z], [pos x, neg y, neg z]].all (evalClause τ) = true := by
  simp only [List.all_cons, List.all_nil, evalClause, List.any_cons, List.any_nil,
    evalLit_pos6 τ hx, evalLit_pos6 τ hy, evalLit_pos6 τ hz,
    evalLit_neg6 τ hx, evalLit_neg6 τ hy, evalLit_neg6 τ hz, h]
  cases τ y <;> cases τ z <;> rfl

/-- `x ↔ y ∧ ¬z`: clauses `[-x, y], [-x, -z], [x, -y, z]`. -/
theorem gate_and_not {x y z : Nat} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : τ x = (τ y && !τ z)) :
    [[neg x, pos y], [neg x, neg z], [pos x, neg y, pos z]].all (evalClause τ) = true := by
  simp only [List.all_cons, List.all_nil, evalClause, List.any_cons, List.any_nil,
    evalLit_pos6 τ hx, evalLit_pos6 τ hy, evalLit_pos6 τ hz,
    evalLit_neg6 τ hx, evalLit_neg6 τ hy, evalLit_neg6 τ hz, h]
  cases τ y <;> cases τ z <;> rfl

/-- `x ↔ ¬y ∧ ¬z`: clauses `[-x, -y], [-x, -z], [x, y, z]`. -/
theorem gate_nor {x y z : Nat} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : τ x = (!τ y && !τ z)) :
    [[neg x, neg y], [neg x, neg z], [pos x, pos y, pos z]].all (evalClause τ) = true := by
  simp only [List.all_cons, List.all_nil, evalClause, List.any_cons, List.any_nil,
    evalLit_pos6 τ hx, evalLit_pos6 τ hy, evalLit_pos6 τ hz,
    evalLit_neg6 τ hx, evalLit_neg6 τ hy, evalLit_neg6 τ hz, h]
  cases τ y <;> cases τ z <;> rfl

/-- `x ↔ y`: clauses `[-y, x], [-x, y]`. -/
theorem gate_eq {x y : Nat} (hx : 0 < x) (hy : 0 < y) (h : τ x = τ y) :
    [[neg y, pos x], [neg x, pos y]].all (evalClause τ) = true := by
  simp only [List.all_cons, List.all_nil, evalClause, List.any_cons, List.any_nil,
    evalLit_pos6 τ hx, evalLit_pos6 τ hy, evalLit_neg6 τ hx, evalLit_neg6 τ hy, h]
  cases τ y <;> rfl

/-- `List.any` only depends on the values of the predicate on the members. -/
theorem FamGates6.any_congr_mem {l : List Nat} {f g : Nat → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- `x ↔ ⋁ ys`: clauses `[-y, x]` for every `y ∈ ys`, and `[-x, ys…]`. -/
theorem gate_or {x : Nat} {ys : List Nat} (hx : 0 < x) (hys : ∀ y ∈ ys, 0 < y)
    (h : τ x = ys.any τ) :
    ((ys.map fun y => [neg y, pos x]) ++ [neg x :: ys.map pos]).all (evalClause τ) = true := by
  rw [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro c hc
    rw [List.mem_map] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
      evalLit_pos6 τ hx, evalLit_neg6 τ (hys y hy), h]
    by_cases hyt : τ y = true
    · rw [List.any_eq_true.2 ⟨y, hy, hyt⟩, Bool.or_true]
    · rw [Bool.not_eq_true] at hyt
      rw [hyt]; rfl
  · simp only [evalClause, List.any_cons, evalLit_neg6 τ hx, List.any_map, h]
    have hc : ys.any (evalLit τ ∘ pos) = ys.any τ :=
      FamGates6.any_congr_mem fun y hy => by
        rw [Function.comp_apply, evalLit_pos6 τ (hys y hy)]
    rw [hc]
    cases ys.any τ <;> rfl

/-- `gate_or` for `ys = l.map f`, with `τ ∘ f` described pointwise on `l`
(the shape of the `before` / `beforeW` families: `cs = (range (F+1)).map (cVar …)`). -/
theorem gate_or_map {x : Nat} {l : List Nat} {f : Nat → Nat} {g : Nat → Bool}
    (hx : 0 < x) (hf : ∀ i ∈ l, 0 < f i) (hxl : τ x = l.any g)
    (hfg : ∀ i ∈ l, τ (f i) = g i) :
    (((l.map f).map fun y => [neg y, pos x]) ++ [neg x :: (l.map f).map pos]).all
      (evalClause τ) = true := by
  apply gate_or τ hx
  · intro y hy
    rw [List.mem_map] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact hf i hi
  · rw [hxl, List.any_map]
    exact (FamGates6.any_congr_mem fun i hi => by rw [Function.comp_apply, hfg i hi]).symm

end Gates

/-! ## Helpers: layout, positivity of ids, evaluation of `tau6` on derived ids -/

namespace FamGates6

theorem layout6_n : (layout 6).n = 6 := by rw [layout6_eq]
theorem layout6_F : (layout 6).F = 15 := by rw [layout6_eq]

theorem vVar_pos (t m w : Nat) : 0 < vVar (layout 6) t m w := by rw [vVar6]; omega
theorem cVar_pos (m a b t : Nat) : 0 < cVar (layout 6) m a b t := by rw [cVar6]; omega
theorem beforeVar_pos (m a b : Nat) : 0 < beforeVar (layout 6) m a b := by
  rw [beforeVar6]; omega
theorem neitherVar_pos (m a b : Nat) : 0 < neitherVar (layout 6) m a b := by
  rw [neitherVar6]; omega
theorem pmVar_pos (m a b : Nat) : 0 < pmVar (layout 6) m a b := by rw [pmVar6]; omega
theorem cWVar_pos (w a b t : Nat) : 0 < cWVar (layout 6) w a b t := by rw [cWVar6]; omega
theorem beforeWVar_pos (w a b : Nat) : 0 < beforeWVar (layout 6) w a b := by
  rw [beforeWVar6]; omega
theorem pwVar_pos (w a b i : Nat) : 0 < pwVar (layout 6) w a b i := by rw [pwVar6]; omega

variable {k : Nat} {S : List (List Nat)} {idxs : List Nat}

theorem tau6_vVar {t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    tau6 k S idxs (vVar (layout 6) t m w) = vis S t m w := by
  unfold tau6; rw [dec_vVar ht hm hw]; rfl

theorem tau6_cVar {m a b t : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6)
    (ht : t ≤ 15) :
    tau6 k S idxs (cVar (layout 6) m a b t) = (vis S t m a && !vis S t m b) := by
  unfold tau6; rw [dec_cVar hm hab ha hb ht]; rfl

theorem tau6_beforeVar {m a b : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (beforeVar (layout 6) m a b) = befB S m a b := by
  unfold tau6; rw [dec_beforeVar hm hab ha hb]; rfl

theorem tau6_neitherVar {m a b : Nat} (hm : m < 6) (hab : a < b) (hb : b < 6) :
    tau6 k S idxs (neitherVar (layout 6) m a b) = (!vis S 15 m a && !vis S 15 m b) := by
  unfold tau6; rw [dec_neitherVar hm hab hb]; rfl

theorem tau6_pmVar {m a b : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (pmVar (layout 6) m a b) =
      (befB S m a b || (decide (a < b) && (!vis S 15 m a && !vis S 15 m b))) := by
  unfold tau6; rw [dec_pmVar hm hab ha hb]; rfl

theorem tau6_cWVar {w a b t : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6)
    (ht : t ≤ 15) :
    tau6 k S idxs (cWVar (layout 6) w a b t) = (vis S t a w && !vis S t b w) := by
  unfold tau6; rw [dec_cWVar hw hab ha hb ht]; rfl

theorem tau6_beforeWVar {w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (beforeWVar (layout 6) w a b) = befWB S w a b := by
  unfold tau6; rw [dec_beforeWVar hw hab ha hb]; rfl

theorem tau6_pwVar0 {w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (pwVar (layout 6) w a b 0) =
      ((befWB S w b a && vis S 15 a w) || (vis S 15 a w && !vis S 15 b w)
        || (decide (a < b) && (!vis S 15 a w && !vis S 15 b w))) := by
  unfold tau6; rw [dec_pwVar0 hw hab ha hb]; rfl

theorem tau6_pwVar1 {w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (pwVar (layout 6) w a b 1) = (befWB S w b a && vis S 15 a w) := by
  unfold tau6; rw [dec_pwVar1 hw hab ha hb]; rfl

theorem tau6_pwVar2 {w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    tau6 k S idxs (pwVar (layout 6) w a b 2) = (vis S 15 a w && !vis S 15 b w) := by
  unfold tau6; rw [dec_pwVar2 hw hab ha hb]; rfl

theorem tau6_pwVar3 {w a b : Nat} (hw : w < 6) (hab : a < b) (hb : b < 6) :
    tau6 k S idxs (pwVar (layout 6) w a b 3) = (!vis S 15 a w && !vis S 15 b w) := by
  unfold tau6; rw [dec_pwVar3 hw hab hb]; rfl

end FamGates6

open FamGates6

/-! ## The five families -/

section Families

variable {k : Nat} {S : List (List Nat)} {idxs : List Nat}

/-- Item 5: `beforeClauses` — `C_t ↔ V_t[m][a] ∧ ¬V_t[m][b]` and `before ↔ ⋁_t C_t`. -/
theorem before_sat : (beforeClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  simp only [beforeClauses, layout6_n, layout6_F, List.all_flatMap]
  refine List.all_eq_true.2 fun m hm => List.all_eq_true.2 fun a ha =>
    List.all_eq_true.2 fun b hb => ?_
  rw [List.mem_range] at hm ha hb
  by_cases hab : a = b
  · rw [if_pos hab]; rfl
  · rw [if_neg hab, List.append_assoc, List.all_append, Bool.and_eq_true]
    constructor
    · simp only [List.all_flatMap]
      refine List.all_eq_true.2 fun t ht => ?_
      rw [List.mem_range] at ht
      exact gate_and_not _ (cVar_pos m a b t) (vVar_pos t m a) (vVar_pos t m b)
        (by rw [tau6_cVar hm hab ha hb (by omega), tau6_vVar (by omega) hm ha,
          tau6_vVar (by omega) hm hb])
    · exact gate_or_map _ (beforeVar_pos m a b) (fun t _ => cVar_pos m a b t)
        (by rw [tau6_beforeVar hm hab ha hb]; rfl)
        (fun t ht => tau6_cVar hm hab ha hb (by rw [List.mem_range] at ht; omega))

/-- Item 6: `neitherClauses` — `neither ↔ ¬V_F[m][a] ∧ ¬V_F[m][b]` (`a < b`). -/
theorem neither_sat : (neitherClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  simp only [neitherClauses, layout6_n, layout6_F, List.all_flatMap]
  refine List.all_eq_true.2 fun m hm => List.all_eq_true.2 fun a ha =>
    List.all_eq_true.2 fun b hb => ?_
  rw [List.mem_range] at hm ha hb
  by_cases hab : a < b
  · rw [if_pos hab]
    exact gate_nor _ (neitherVar_pos m a b) (vVar_pos 15 m a) (vVar_pos 15 m b)
      (by rw [tau6_neitherVar hm hab hb, tau6_vVar (le_refl 15) hm ha,
        tau6_vVar (le_refl 15) hm hb])
  · rw [if_neg hab]; rfl

/-- Item 7: `pmClauses` — `PM ↔ before ∨ neither` for `a < b`, `PM ↔ before` for `a > b`. -/
theorem pm_sat : (pmClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  simp only [pmClauses, layout6_n, List.all_flatMap]
  refine List.all_eq_true.2 fun m hm => List.all_eq_true.2 fun a ha =>
    List.all_eq_true.2 fun b hb => ?_
  rw [List.mem_range] at hm ha hb
  by_cases hab : a = b
  · rw [if_pos hab]; rfl
  · rw [if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt]
      exact gate_or _ (ys := [beforeVar (layout 6) m a b, neitherVar (layout 6) m a b])
        (pmVar_pos m a b)
        (by
          intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact beforeVar_pos m a b
          · exact neitherVar_pos m a b)
        (by
          rw [tau6_pmVar hm hab ha hb, List.any_cons, List.any_cons, List.any_nil,
            tau6_beforeVar hm hab ha hb, tau6_neitherVar hm hlt hb, decide_eq_true hlt,
            Bool.true_and, Bool.or_false])
    · rw [if_neg hlt]
      exact gate_eq _ (pmVar_pos m a b) (beforeVar_pos m a b)
        (by
          rw [tau6_pmVar hm hab ha hb, tau6_beforeVar hm hab ha hb, decide_eq_false hlt,
            Bool.false_and, Bool.or_false])

/-- Item 8: `beforeWClauses` — as item 5 on the women's side (`VW_t[w][m] := V_t[m][w]`). -/
theorem beforeW_sat : (beforeWClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  simp only [beforeWClauses, layout6_n, layout6_F, List.all_flatMap]
  refine List.all_eq_true.2 fun w hw => List.all_eq_true.2 fun a ha =>
    List.all_eq_true.2 fun b hb => ?_
  rw [List.mem_range] at hw ha hb
  by_cases hab : a = b
  · rw [if_pos hab]; rfl
  · rw [if_neg hab, List.append_assoc, List.all_append, Bool.and_eq_true]
    constructor
    · simp only [List.all_flatMap]
      refine List.all_eq_true.2 fun t ht => ?_
      rw [List.mem_range] at ht
      exact gate_and_not _ (cWVar_pos w a b t) (vVar_pos t a w) (vVar_pos t b w)
        (by rw [tau6_cWVar hw hab ha hb (by omega), tau6_vVar (by omega) ha hw,
          tau6_vVar (by omega) hb hw])
    · exact gate_or_map _ (beforeWVar_pos w a b) (fun t _ => cWVar_pos w a b t)
        (by rw [tau6_beforeWVar hw hab ha hb]; rfl)
        (fun t ht => tau6_cWVar hw hab ha hb (by rw [List.mem_range] at ht; omega))

/-- Item 9: `pwClauses` — `later ↔ beforeW(w,b,a) ∧ V_F[a][w]`, `only_a ↔ V_F[a][w] ∧ ¬V_F[b][w]`,
`nv ↔ ¬V_F[a][w] ∧ ¬V_F[b][w]` (only for `a < b`), and `PW ↔ ⋁ terms`. -/
theorem pw_sat : (pwClauses (layout 6)).all (evalClause (tau6 k S idxs)) = true := by
  simp only [pwClauses, layout6_n, layout6_F, List.all_flatMap]
  refine List.all_eq_true.2 fun w hw => List.all_eq_true.2 fun a ha =>
    List.all_eq_true.2 fun b hb => ?_
  rw [List.mem_range] at hw ha hb
  by_cases hab : a = b
  · rw [if_pos hab]; rfl
  · rw [if_neg hab]
    have hba : b ≠ a := Ne.symm hab
    -- the `later` gate
    have hLater : [[neg (pwVar (layout 6) w a b 1), pos (beforeWVar (layout 6) w b a)],
        [neg (pwVar (layout 6) w a b 1), pos (vVar (layout 6) 15 a w)],
        [pos (pwVar (layout 6) w a b 1), neg (beforeWVar (layout 6) w b a),
          neg (vVar (layout 6) 15 a w)]].all (evalClause (tau6 k S idxs)) = true :=
      gate_and2 _ (pwVar_pos w a b 1) (beforeWVar_pos w b a) (vVar_pos 15 a w)
        (by rw [tau6_pwVar1 hw hab ha hb, tau6_beforeWVar hw hba hb ha,
          tau6_vVar (le_refl 15) ha hw])
    -- the `only_a` gate
    have hOnlyA : [[neg (pwVar (layout 6) w a b 2), pos (vVar (layout 6) 15 a w)],
        [neg (pwVar (layout 6) w a b 2), neg (vVar (layout 6) 15 b w)],
        [pos (pwVar (layout 6) w a b 2), neg (vVar (layout 6) 15 a w),
          pos (vVar (layout 6) 15 b w)]].all (evalClause (tau6 k S idxs)) = true :=
      gate_and_not _ (pwVar_pos w a b 2) (vVar_pos 15 a w) (vVar_pos 15 b w)
        (by rw [tau6_pwVar2 hw hab ha hb, tau6_vVar (le_refl 15) ha hw,
          tau6_vVar (le_refl 15) hb hw])
    by_cases hlt : a < b
    · simp only [if_pos hlt]
      -- the `nv` gate (present only for `a < b`)
      have hNv : [[neg (pwVar (layout 6) w a b 3), neg (vVar (layout 6) 15 a w)],
          [neg (pwVar (layout 6) w a b 3), neg (vVar (layout 6) 15 b w)],
          [pos (pwVar (layout 6) w a b 3), pos (vVar (layout 6) 15 a w),
            pos (vVar (layout 6) 15 b w)]].all (evalClause (tau6 k S idxs)) = true :=
        gate_nor _ (pwVar_pos w a b 3) (vVar_pos 15 a w) (vVar_pos 15 b w)
          (by rw [tau6_pwVar3 hw hlt hb, tau6_vVar (le_refl 15) ha hw,
            tau6_vVar (le_refl 15) hb hw])
      -- `PW ↔ later ∨ only_a ∨ nv`
      have hPW := gate_or (tau6 k S idxs)
        (ys := [pwVar (layout 6) w a b 1, pwVar (layout 6) w a b 2, pwVar (layout 6) w a b 3])
        (pwVar_pos w a b 0)
        (by
          intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl
          · exact pwVar_pos w a b 1
          · exact pwVar_pos w a b 2
          · exact pwVar_pos w a b 3)
        (by
          rw [tau6_pwVar0 hw hab ha hb, List.any_cons, List.any_cons, List.any_cons,
            List.any_nil, tau6_pwVar1 hw hab ha hb, tau6_pwVar2 hw hab ha hb,
            tau6_pwVar3 hw hlt hb, decide_eq_true hlt, Bool.true_and, Bool.or_false,
            Bool.or_assoc])
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.all_append,
        List.all_append, List.all_append, hLater, hOnlyA, hNv, Bool.true_and, Bool.true_and,
        Bool.true_and]
      exact hPW
    · simp only [if_neg hlt]
      -- `PW ↔ later ∨ only_a`
      have hPW := gate_or (tau6 k S idxs)
        (ys := [pwVar (layout 6) w a b 1, pwVar (layout 6) w a b 2])
        (pwVar_pos w a b 0)
        (by
          intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact pwVar_pos w a b 1
          · exact pwVar_pos w a b 2)
        (by
          rw [tau6_pwVar0 hw hab ha hb, List.any_cons, List.any_cons, List.any_nil,
            tau6_pwVar1 hw hab ha hb, tau6_pwVar2 hw hab ha hb, decide_eq_false hlt,
            Bool.false_and, Bool.or_false, Bool.or_false])
      rw [List.append_nil, List.append_assoc, List.append_assoc, List.all_append,
        List.all_append, hLater, hOnlyA, Bool.true_and, Bool.true_and]
      exact hPW

end Families
