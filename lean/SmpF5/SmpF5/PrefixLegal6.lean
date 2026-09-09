import SmpF5.Cubes6
import SmpF5.SchedLen6

/-!
# Prefix legality (plan §5.3, L5.10–L5.12)

The cube filter `Cubes6.legalPrefixB` is the Bool mirror of the checks
of `cube_campaign.apply_step`; the coverage argument (plan L3.17) needs
that every prefix of a `Legal` schedule passes it.  This file proves:

* **L5.10** `schedMatchings_take`: the matching sequence of a prefix is
  the corresponding prefix of the matching sequence (`scanl` commutes
  with `take`, up to the extra initial matching);
* `strajM_take_prefix` / `strajW_take_prefix`: trajectories of a prefix
  schedule are prefixes of the trajectories (via the private
  `destutter_take_prefix`, plan L5.1/L5.2, proved here because
  `DestutterPrefix6` does not provide it);
* **L5.11** `Legal_take`: legality is inherited by prefixes;
* `WFStepB_iff`: the Bool step check decides `WFStep`;
* **L5.12** `legalPrefixB_of_Legal`: a legal schedule passes the cube
  filter (budget from `moves_le_30`, cap from `strajM_length_le_6`,
  revisit-freeness from `Legal`).

Also a few trivial facts about `(S.take k).flatten` used when reasoning
about `Cubes6.usedBefore`/`newMen`.
-/

open Cubes6

/-! ## Private helpers: `scanl`/`destutter'` and prefixes -/

namespace PrefixLegal6

/-- `scanl` commutes with `take` (the result keeps the initial value). -/
private theorem scanl_take {α β : Type} (f : α → β → α) :
    ∀ (l : List β) (a : α) (k : Nat),
    (l.take k).scanl f a = (l.scanl f a).take (k + 1) := by
  intro l
  induction l with
  | nil =>
    intro a k
    rw [List.take_nil, List.scanl_nil, List.take_succ_cons, List.take_nil]
  | cons b l ih =>
    intro a k
    cases k with
    | zero =>
      rw [List.take_zero, List.scanl_nil, List.scanl_cons, List.take_succ_cons,
        List.take_zero]
    | succ k =>
      rw [List.take_succ_cons, List.scanl_cons, List.scanl_cons, ih,
        List.take_succ_cons]

/-- `destutter' R a l` starts with `a`. -/
private theorem singleton_prefix_destutter' {α : Type} (R : α → α → Prop)
    [DecidableRel R] : ∀ (l : List α) (a : α), [a] <+: l.destutter' R a := by
  intro l
  induction l with
  | nil => intro a; rw [List.destutter'_nil]
  | cons b l ih =>
    intro a
    by_cases hab : R a b
    · rw [List.destutter'_cons_pos (l := l) hab]
      exact List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩
    · rw [List.destutter'_cons_neg (l := l) hab]
      exact ih a

/-- L5.1: prefixes are preserved by `destutter'`. -/
private theorem destutter'_take_prefix {α : Type} (R : α → α → Prop)
    [DecidableRel R] : ∀ (l : List α) (a : α) (k : Nat),
    (l.take k).destutter' R a <+: l.destutter' R a := by
  intro l
  induction l with
  | nil => intro a k; rw [List.take_nil]
  | cons b l ih =>
    intro a k
    cases k with
    | zero =>
      rw [List.take_zero, List.destutter'_nil]
      exact singleton_prefix_destutter' R (b :: l) a
    | succ k =>
      rw [List.take_succ_cons]
      by_cases hab : R a b
      · rw [List.destutter'_cons_pos (l := l.take k) hab,
          List.destutter'_cons_pos (l := l) hab]
        exact List.cons_prefix_cons.2 ⟨rfl, ih b k⟩
      · rw [List.destutter'_cons_neg (l := l.take k) hab,
          List.destutter'_cons_neg (l := l) hab]
        exact ih a k

/-- L5.2: prefixes are preserved by `destutter`. -/
private theorem destutter_take_prefix {α : Type} (R : α → α → Prop)
    [DecidableRel R] (l : List α) (k : Nat) :
    (l.take k).destutter R <+: l.destutter R := by
  cases l with
  | nil => rw [List.take_nil]
  | cons a l =>
    cases k with
    | zero => rw [List.take_zero, List.destutter_nil]; exact List.nil_prefix
    | succ k =>
      rw [List.take_succ_cons, List.destutter_cons', List.destutter_cons']
      exact destutter'_take_prefix R l a k

end PrefixLegal6

/-! ## L5.10: the matching sequence of a prefix -/

theorem schedMatchings_take (S : List (List Nat)) (k : Nat) :
    schedMatchings (S.take k) = (schedMatchings S).take (k + 1) := by
  unfold schedMatchings
  exact PrefixLegal6.scanl_take _ S idRow6 k

/-- A partner column of a prefix schedule is the prefix of the column. -/
theorem schedMatchings_take_map {β : Type} (S : List (List Nat)) (k : Nat)
    (g : List Nat → β) :
    (schedMatchings (S.take k)).map g = ((schedMatchings S).map g).take (k + 1) := by
  rw [schedMatchings_take, List.map_take]

theorem strajM_take_prefix (S : List (List Nat)) (k m : Nat) :
    strajM (S.take k) m <+: strajM S m := by
  unfold strajM
  rw [schedMatchings_take_map]
  exact PrefixLegal6.destutter_take_prefix _ _ _

theorem strajW_take_prefix (S : List (List Nat)) (k w : Nat) :
    strajW (S.take k) w <+: strajW S w := by
  unfold strajW
  rw [schedMatchings_take_map]
  exact PrefixLegal6.destutter_take_prefix _ _ _

/-! ## L5.11: legality of prefixes -/

theorem Legal_take {S : List (List Nat)} (hL : Legal S) (k : Nat) :
    Legal (S.take k) := by
  obtain ⟨hWF, hM, hW⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · intro st hst
    exact hWF st (List.mem_of_mem_take hst)
  · intro m hm
    exact (hM m hm).sublist (strajM_take_prefix S k m).sublist
  · intro w hw
    exact (hW w hw).sublist (strajW_take_prefix S k w).sublist

/-! ## L5.12: a legal schedule passes the cube filter -/

theorem WFStepB_iff (st : List Nat) : WFStepB st = true ↔ WFStep st := by
  simp only [WFStepB, WFStep, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact and_assoc

theorem legalPrefixB_of_Legal {S : List (List Nat)} (hL : Legal S) :
    legalPrefixB S = true := by
  simp only [legalPrefixB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨⟨?_, moves_le_30 hL⟩, ?_⟩, ?_⟩
  · intro st hst
    exact (WFStepB_iff st).2 (hL.1 st hst)
  · intro m hm
    exact ⟨hL.2.1 m hm, strajM_length_le_6 hL hm⟩
  · intro w hw
    exact hL.2.2 w hw

/-- The converse direction of the step check, for convenience. -/
theorem WFStep_of_WFStepB {st : List Nat} (h : WFStepB st = true) : WFStep st :=
  (WFStepB_iff st).1 h

/-! ## Trivial facts about `(S.take k).flatten` -/

theorem mem_take_flatten {S : List (List Nat)} {k x : Nat} :
    x ∈ (S.take k).flatten ↔ ∃ st ∈ S.take k, x ∈ st :=
  List.mem_flatten

theorem mem_flatten_of_mem_take_flatten {S : List (List Nat)} {k x : Nat}
    (h : x ∈ (S.take k).flatten) : x ∈ S.flatten := by
  obtain ⟨st, hst, hx⟩ := List.mem_flatten.1 h
  exact List.mem_flatten.2 ⟨st, List.mem_of_mem_take hst, hx⟩

theorem take_flatten_mono {S : List (List Nat)} {j k x : Nat} (hjk : j ≤ k)
    (h : x ∈ (S.take j).flatten) : x ∈ (S.take k).flatten := by
  obtain ⟨st, hst, hx⟩ := List.mem_flatten.1 h
  refine List.mem_flatten.2 ⟨st, ?_, hx⟩
  have : S.take j = (S.take k).take j := by
    rw [List.take_take, Nat.min_eq_left hjk]
  rw [this] at hst
  exact List.mem_of_mem_take hst

theorem mem_take_flatten_of_lt {S : List (List Nat)} {t k x : Nat} (htk : t < k)
    (ht : t < S.length) (hx : x ∈ S.getD t []) : x ∈ (S.take k).flatten := by
  refine List.mem_flatten.2 ⟨S.getD t [], ?_, hx⟩
  rw [List.getD_eq_getElem _ _ ht]
  have hlen : t < (S.take k).length := by
    rw [List.length_take]; omega
  have : (S.take k)[t] = S[t] := List.getElem_take
  rw [← this]
  exact List.getElem_mem hlen
