import SmpMax.Six.VariableDecoding
import SmpMax.Six.CyclicShapes
import SmpMax.Six.TrajectoryPrefixes

/-!
# Frames, visited masks, and the assignment (plan §4.4)

The CNF's state at frame `t` is the matching `frame S t` (frames past the
end of the schedule copy the last matching) and the visited mask `vis S t
m w` = "`w` occurs among `m`'s first `t+1` partners".  `τV` assigns every
decoded variable by the gate formula the Python encoder uses for it, so
that the definitional clause families hold by unfolding; the semantic
content (derived comparisons = read-off ranks) is proved separately.
-/

open SchedCNF6

def frame (S : List (List Nat)) (t : Nat) : List Nat :=
  (schedMatchings S).getD (min t S.length) []

/-- `m`'s partner column over the matching sequence. -/
def colM (S : List (List Nat)) (m : Nat) : List Nat :=
  (schedMatchings S).map (fun mu => mu.getD m 0)

def vis (S : List (List Nat)) (t m w : Nat) : Bool :=
  decide (w ∈ (colM S m).take (t + 1))

/-- The one-hot step index at frame `t`: `0` = stop, `j ≥ 1` = shape
`(cyclicShapes 6)[j-1]` (as `prefixUnits`: `idxOf … + 1`). -/
def stepIdx (S : List (List Nat)) (t : Nat) : Nat :=
  if t < S.length then (cyclicShapes 6).idxOf (minFirst (S.getD t [])) + 1 else 0

def befB (S : List (List Nat)) (m a b : Nat) : Bool :=
  (List.range 16).any (fun t => vis S t m a && !vis S t m b)

def befWB (S : List (List Nat)) (w a b : Nat) : Bool :=
  (List.range 16).any (fun t => vis S t a w && !vis S t b w)

/-- The assignment on decoded variables (`sched_sat.build`'s gates, F = 15). -/
def τV (S : List (List Nat)) (idxs : List Nat) : V6 → Bool
  | .M t m w      => decide ((frame S t).getD m 0 = w)
  | .Vis t m w    => vis S t m w
  | .St t j       => decide (j = stepIdx S t)
  | .C m a b t    => vis S t m a && !vis S t m b
  | .Bef m a b    => befB S m a b
  | .Nei m a b    => !vis S 15 m a && !vis S 15 m b
  | .PM m a b     => befB S m a b || (decide (a < b) && (!vis S 15 m a && !vis S 15 m b))
  | .CW w a b t   => vis S t a w && !vis S t b w
  | .BefW w a b   => befWB S w a b
  | .Later w a b  => befWB S w b a && vis S 15 a w
  | .OnlyA w a b  => vis S 15 a w && !vis S 15 b w
  | .NeiW w a b   => !vis S 15 a w && !vis S 15 b w
  | .PW w a b     => (befWB S w b a && vis S 15 a w) || (vis S 15 a w && !vis S 15 b w)
                     || (decide (a < b) && (!vis S 15 a w && !vis S 15 b w))
  | .Y t i        => decide (idxs.getD t 720 = i)
  | .Pf t i       => decide (idxs.getD t 720 ≤ i)
  | .junk         => false

def tau6 (k : Nat) (S : List (List Nat)) (idxs : List Nat) : Nat → Bool :=
  fun v => τV S idxs (dec6 k v)

/-! ## Literals (plan L4.4) -/

theorem evalLit_pos6 (τ : Nat → Bool) {v : Nat} (hv : 0 < v) : evalLit τ (pos v) = τ v := by
  unfold evalLit pos
  have h : (0 : Int) < (v : Int) := by exact_mod_cast hv
  have hv0 : v ≠ 0 := by omega
  simp [h, hv0]

theorem evalLit_neg6 (τ : Nat → Bool) {v : Nat} (hv : 0 < v) : evalLit τ (neg v) = !τ v := by
  unfold evalLit neg
  have h : ¬ ((0 : Int) < -(v : Int)) := by omega
  simp

/-! ## The matching sequence as a function of `t` -/

theorem schedMatchings_length (S : List (List Nat)) : (schedMatchings S).length = S.length + 1 := by
  unfold schedMatchings; exact List.length_scanl

theorem scanl_getD_zero {α β : Type} (f : α → β → α) (a : α) (l : List β) (d : α) :
    (l.scanl f a).getD 0 d = a := by
  cases l <;> simp [List.scanl_cons, List.scanl_nil]

theorem scanl_getD_succ {α β : Type} (f : α → β → α) (d : α) (d' : β) :
    ∀ (l : List β) (a : α) (t : Nat), t < l.length →
    (l.scanl f a).getD (t + 1) d = f ((l.scanl f a).getD t d) (l.getD t d') := by
  intro l
  induction l with
  | nil => intro a t ht; simp at ht
  | cons b l ih =>
    intro a t ht
    rw [List.scanl_cons]
    cases t with
    | zero =>
      simp only [List.getD_cons_succ, List.getD_cons_zero, scanl_getD_zero]
    | succ t =>
      simp only [List.getD_cons_succ]
      exact ih (f a b) t (by simpa using ht)

theorem frame_zero (S : List (List Nat)) : frame S 0 = idRow6 := by
  unfold frame schedMatchings
  simp only [Nat.zero_min]
  exact scanl_getD_zero _ _ _ _

theorem frame_getD_of_le {S : List (List Nat)} {t : Nat} (ht : t ≤ S.length) :
    frame S t = (schedMatchings S).getD t [] := by
  unfold frame; rw [Nat.min_eq_left ht]

theorem frame_of_le {S : List (List Nat)} {t : Nat} (ht : S.length ≤ t) :
    frame S t = frame S S.length := by
  unfold frame; rw [Nat.min_eq_right ht, Nat.min_self]

theorem frame_mem (S : List (List Nat)) (t : Nat) : frame S t ∈ schedMatchings S := by
  unfold frame
  have hlt : min t S.length < (schedMatchings S).length := by
    rw [schedMatchings_length]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

theorem frame_perm {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) (t : Nat) :
    (frame S t).Perm idRow6 :=
  schedMatchings_perm hWF _ (frame_mem S t)

theorem frame_succ_step {S : List (List Nat)} {t : Nat} (ht : t < S.length) :
    frame S (t + 1) = applyStep (S.getD t []) (frame S t) := by
  rw [frame_getD_of_le (by omega), frame_getD_of_le (by omega)]
  unfold schedMatchings
  exact scanl_getD_succ _ [] [] S idRow6 t ht

theorem frame_succ_stop {S : List (List Nat)} {t : Nat} (ht : S.length ≤ t) :
    frame S (t + 1) = frame S t := by
  rw [frame_of_le (by omega), frame_of_le ht]

/-! ## Step indices -/

theorem stepIdx_le {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) (t : Nat) :
    stepIdx S t ≤ 409 := by
  unfold stepIdx
  split
  · next ht =>
    have hmem : minFirst (S.getD t []) ∈ cyclicShapes 6 := by
      apply minFirst_mem_cyclicShapes
      apply hWF
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    have := List.idxOf_lt_length_iff.2 hmem
    rw [cyclicShapes6_length] at this
    omega
  · omega

theorem stepIdx_pos_iff (S : List (List Nat)) (t : Nat) : 0 < stepIdx S t ↔ t < S.length := by
  unfold stepIdx; split <;> simp_all

theorem shape_of_stepIdx {S : List (List Nat)} {t : Nat} (hWF : ∀ st ∈ S, WFStep st)
    (ht : t < S.length) :
    (cyclicShapes 6).getD (stepIdx S t - 1) [] = minFirst (S.getD t []) := by
  unfold stepIdx
  rw [if_pos ht, Nat.add_sub_cancel]
  have hmem : minFirst (S.getD t []) ∈ cyclicShapes 6 := by
    apply minFirst_mem_cyclicShapes
    apply hWF
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  have hlt := List.idxOf_lt_length_iff.2 hmem
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

/-! ## Visited masks -/

theorem colM_length (S : List (List Nat)) (m : Nat) : (colM S m).length = S.length + 1 := by
  unfold colM; rw [List.length_map, schedMatchings_length]

theorem colM_getD {S : List (List Nat)} {m t : Nat} (ht : t ≤ S.length) :
    (colM S m).getD t 0 = (frame S t).getD m 0 := by
  unfold colM
  rw [frame_getD_of_le ht]
  have hlt : t < (schedMatchings S).length := by rw [schedMatchings_length]; omega
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map,
    List.getD_eq_getElem _ _ hlt]

theorem strajM_eq_destutter_colM (S : List (List Nat)) (m : Nat) :
    strajM S m = (colM S m).destutter (· ≠ ·) := rfl

theorem vis_zero {S : List (List Nat)} {m w : Nat} (hm : m < 6) :
    vis S 0 m w = decide (w = m) := by
  unfold vis colM
  have h0 : (schedMatchings S).take 1 = [idRow6] := by
    have := schedMatchings_head S
    cases h : schedMatchings S with
    | nil => rw [h] at this; simp at this
    | cons x xs => rw [h] at this; simp at this; simp [this]
  rw [← List.map_take, h0]
  simp only [List.map_cons, List.map_nil, List.mem_singleton]
  have : idRow6.getD m 0 = m := by
    rw [idRow6_eq_range, List.getD_eq_getElem _ _ (by simpa using hm)]; simp
  rw [this]

theorem vis_succ {S : List (List Nat)} (t m w : Nat) :
    vis S (t + 1) m w = (vis S t m w || decide ((frame S (t + 1)).getD m 0 = w)) := by
  unfold vis
  rw [List.take_add_one (i := t + 1)]
  by_cases ht : t + 1 < (colM S m).length
  · have hget : (colM S m)[t + 1]? = some ((frame S (t + 1)).getD m 0) := by
      rw [List.getElem?_eq_getElem ht, ← List.getD_eq_getElem _ _ ht]
      rw [colM_getD (by rw [colM_length] at ht; omega)]
    rw [hget]
    simp only [Option.toList, List.mem_append, List.mem_singleton]
    by_cases h1 : w ∈ (colM S m).take (t + 1) <;> by_cases h2 : (frame S (t + 1)).getD m 0 = w <;>
      simp [h1, eq_comm]
  · have hnone : (colM S m)[t + 1]? = none := List.getElem?_eq_none (by omega)
    rw [hnone]
    simp only [Option.toList, List.append_nil]
    have hlen : S.length ≤ t := by rw [colM_length] at ht; omega
    -- the last partner is already in the prefix
    have hmem : (frame S (t + 1)).getD m 0 ∈ (colM S m).take (t + 1) := by
      rw [frame_of_le (by omega), ← colM_getD (le_refl _)]
      have hl : S.length < (colM S m).length := by rw [colM_length]; omega
      rw [List.getD_eq_getElem _ _ hl]
      rw [List.take_of_length_le (by rw [colM_length]; omega)]
      exact List.getElem_mem hl
    by_cases h2 : (frame S (t + 1)).getD m 0 = w
    · rw [h2] at hmem
      simp [hmem]
    · rw [decide_eq_false h2]
      simp

theorem vis_full {S : List (List Nat)} {t m w : Nat} (ht : S.length ≤ t) :
    vis S t m w = true ↔ w ∈ strajM S m := by
  unfold vis
  rw [List.take_of_length_le (by rw [colM_length]; omega), strajM_eq_destutter_colM,
    mem_destutter_ne_iff]
  simp

theorem vis_iff_idxOf {S : List (List Nat)} {t m w : Nat} (hw : w ∈ colM S m) :
    vis S t m w = true ↔ idxOf w (colM S m) < t + 1 := by
  unfold vis
  rw [decide_eq_true_iff]
  exact mem_take_iff_idxOf_lt _ _ _ hw

theorem vis_false_of_notMem {S : List (List Nat)} {t m w : Nat} (hw : w ∉ colM S m) :
    vis S t m w = false := by
  unfold vis
  simp only [decide_eq_false_iff_not]
  intro h; exact hw ((List.take_sublist _ _).subset h)
