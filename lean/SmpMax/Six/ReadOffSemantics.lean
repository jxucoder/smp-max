import SmpMax.Six.FrameAssignment

/-!
# The crux: derived comparisons = read-off ranks (plan §5.4)

`PM_sem` / `PW_sem`: under the assignment `τV`, the men's/women's
preference variable `PM(m,a,b)` / `PW(w,a,b)` is true exactly when `a`
precedes `b` in the read-off row `rowOrderM S m` / `rowOrderW S w`.
-/

open SchedCNF6

/-! ## Columns on the women's side -/

/-- `w`'s partner column (`VW_t[w][m] := V[t][m][w]`). -/
def colW (S : List (List Nat)) (w : Nat) : List Nat :=
  (schedMatchings S).map (fun mu => idxOf w mu)

theorem strajW_eq_destutter_colW (S : List (List Nat)) (w : Nat) :
    strajW S w = (colW S w).destutter (· ≠ ·) := rfl

theorem colW_length (S : List (List Nat)) (w : Nat) : (colW S w).length = S.length + 1 := by
  unfold colW; rw [List.length_map, schedMatchings_length]

/-- `vis S t a w` read on the women's side: `a ∈ (colW S w).take (t+1)`. -/
theorem vis_iff_mem_take_colW {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st)
    {t a w : Nat} (ha : a < 6) (hw : w < 6) :
    vis S t a w = true ↔ a ∈ (colW S w).take (t + 1) := by
  unfold vis colM colW
  rw [decide_eq_true_iff, ← List.map_take, ← List.map_take]
  simp only [List.mem_map]
  constructor
  · rintro ⟨mu, hmu, h⟩
    have hp : mu.Perm idRow6 :=
      schedMatchings_perm hWF mu ((List.take_sublist _ _).subset hmu)
    refine ⟨mu, hmu, ?_⟩
    rw [← h]; exact partner_idxOf hp ha
  · rintro ⟨mu, hmu, h⟩
    have hp : mu.Perm idRow6 :=
      schedMatchings_perm hWF mu ((List.take_sublist _ _).subset hmu)
    refine ⟨mu, hmu, ?_⟩
    rw [← h]; exact getD_idxOf (perm6_mem hp hw)

/-! ## `before` on both sides -/

theorem befB_iff {S : List (List Nat)} (hlen : S.length ≤ 15) {m a b : Nat} :
    befB S m a b = true ↔
      a ∈ colM S m ∧ (b ∉ colM S m ∨ idxOf a (colM S m) < idxOf b (colM S m)) := by
  unfold befB
  rw [List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨t, _, hva, hvb⟩
    by_cases hac : a ∈ colM S m
    · refine ⟨hac, ?_⟩
      by_cases hbc : b ∈ colM S m
      · right
        have h1 := (vis_iff_idxOf hac).1 hva
        have h2 : ¬ (idxOf b (colM S m) < t + 1) := by
          intro h
          rw [(vis_iff_idxOf hbc).2 h] at hvb
          exact Bool.noConfusion hvb
        omega
      · left; exact hbc
    · rw [vis_false_of_notMem hac] at hva
      exact Bool.noConfusion hva
  · rintro ⟨hac, hb⟩
    refine ⟨idxOf a (colM S m), ?_, (vis_iff_idxOf hac).2 (by omega), ?_⟩
    · have := idxOf_lt_length hac
      rw [colM_length] at this
      omega
    · by_cases hbc : b ∈ colM S m
      · rcases hb with hb | hb
        · exact absurd hbc hb
        · rw [Bool.eq_false_iff]
          intro h
          have := (vis_iff_idxOf hbc).1 h
          omega
      · exact vis_false_of_notMem hbc

theorem mem_take_colW_iff_idxOf {S : List (List Nat)} {t w a : Nat} (ha : a ∈ colW S w) :
    a ∈ (colW S w).take (t + 1) ↔ idxOf a (colW S w) < t + 1 :=
  mem_take_iff_idxOf_lt _ _ _ ha

theorem befWB_iff {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) (hlen : S.length ≤ 15)
    {w a b : Nat} (hw : w < 6) (ha : a < 6) (hb : b < 6) :
    befWB S w a b = true ↔
      a ∈ colW S w ∧ (b ∉ colW S w ∨ idxOf a (colW S w) < idxOf b (colW S w)) := by
  unfold befWB
  rw [List.any_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  have hva : ∀ t, vis S t a w = true ↔ a ∈ (colW S w).take (t + 1) :=
    fun t => vis_iff_mem_take_colW hWF ha hw
  have hvb : ∀ t, vis S t b w = false ↔ b ∉ (colW S w).take (t + 1) := fun t => by
    rw [Bool.eq_false_iff, ne_eq, vis_iff_mem_take_colW hWF hb hw]
  constructor
  · rintro ⟨t, _, h1, h2⟩
    rw [hva] at h1
    rw [hvb] at h2
    have hac : a ∈ colW S w := (List.take_sublist _ _).subset h1
    refine ⟨hac, ?_⟩
    by_cases hbc : b ∈ colW S w
    · right
      have := (mem_take_colW_iff_idxOf hac).1 h1
      have h2' : ¬ idxOf b (colW S w) < t + 1 :=
        fun h => h2 ((mem_take_colW_iff_idxOf hbc).2 h)
      omega
    · left; exact hbc
  · rintro ⟨hac, hb'⟩
    refine ⟨idxOf a (colW S w), ?_,
      (hva _).2 ((mem_take_colW_iff_idxOf hac).2 (by omega)), (hvb _).2 ?_⟩
    · have := idxOf_lt_length hac
      rw [colW_length] at this
      omega
    · intro hmem
      have hbc : b ∈ colW S w := (List.take_sublist _ _).subset hmem
      rcases hb' with hb' | hb'
      · exact hb' hbc
      · have := (mem_take_colW_iff_idxOf hbc).1 hmem
        omega

/-! ## Positions in a trajectory completed by the missing partners -/

theorem rowOrder_lt_iff {A : List Nat} {a b : Nat} (ha : a < 6) (hb : b < 6) :
    idxOf a (A ++ (List.range 6).filter (fun x => decide (x ∉ A))) <
      idxOf b (A ++ (List.range 6).filter (fun x => decide (x ∉ A))) ↔
    (a ∈ A ∧ (b ∉ A ∨ idxOf a A < idxOf b A)) ∨ (a ∉ A ∧ b ∉ A ∧ a < b) := by
  by_cases haA : a ∈ A <;> by_cases hbA : b ∈ A
  · rw [idxOf_append_mem haA, idxOf_append_mem hbA]
    simp [haA, hbA]
  · rw [idxOf_append_mem haA, idxOf_append_notMem hbA]
    have := idxOf_lt_length haA
    simp only [haA, hbA, not_false_eq_true, true_or, and_self, true_and, false_and, or_false,
      iff_true, not_true_eq_false]
    omega
  · rw [idxOf_append_notMem haA, idxOf_append_mem hbA]
    have := idxOf_lt_length hbA
    simp only [haA, hbA, false_and, false_or, not_true_eq_false, and_false, iff_false, not_lt]
    omega
  · rw [idxOf_append_notMem haA, idxOf_append_notMem hbA]
    have haR : a ∈ (List.range 6).filter (fun x => decide (x ∉ A)) := by
      simp [List.mem_filter, ha, haA]
    have hbR : b ∈ (List.range 6).filter (fun x => decide (x ∉ A)) := by
      simp [List.mem_filter, hb, hbA]
    rw [Nat.add_lt_add_iff_left, idxOf_filter_range_lt haR hbR]
    simp [haA, hbA]

/-! ## The crux lemmas -/

theorem PM_sem {S : List (List Nat)} (hL : Legal S) (hlen : S.length ≤ 15) {idxs : List Nat}
    {m a b : Nat} (hm : m < 6) (ha : a < 6) (hb : b < 6) :
    τV S idxs (.PM m a b) = true ↔ idxOf a (rowOrderM S m) < idxOf b (rowOrderM S m) := by
  unfold rowOrderM
  rw [rowOrder_lt_iff ha hb]
  have hmemA : a ∈ strajM S m ↔ a ∈ colM S m := by
    rw [strajM_eq_destutter_colM, mem_destutter_ne_iff]
  have hmemB : b ∈ strajM S m ↔ b ∈ colM S m := by
    rw [strajM_eq_destutter_colM, mem_destutter_ne_iff]
  have hv15a : vis S 15 m a = false ↔ a ∉ strajM S m := by
    rw [Bool.eq_false_iff, ne_eq, vis_full hlen]
  have hv15b : vis S 15 m b = false ↔ b ∉ strajM S m := by
    rw [Bool.eq_false_iff, ne_eq, vis_full hlen]
  simp only [τV, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_iff]
  rw [befB_iff hlen, hv15a, hv15b]
  by_cases hac : a ∈ colM S m <;> by_cases hbc : b ∈ colM S m
  · have hd := idxOf_destutter_lt_iff hac hbc
    rw [← strajM_eq_destutter_colM] at hd
    have had := hmemA.2 hac
    have hbd := hmemB.2 hbc
    simp [hac, hbc, had, hbd, hd]
  · have had := hmemA.2 hac
    have hbd : b ∉ strajM S m := fun h => hbc (hmemB.1 h)
    simp [hac, hbc, had, hbd]
  · have had : a ∉ strajM S m := fun h => hac (hmemA.1 h)
    have hbd := hmemB.2 hbc
    simp [hac, hbc, had, hbd]
  · have had : a ∉ strajM S m := fun h => hac (hmemA.1 h)
    have hbd : b ∉ strajM S m := fun h => hbc (hmemB.1 h)
    simp [hac, hbc, had, hbd]

theorem PW_sem {S : List (List Nat)} (hL : Legal S) (hlen : S.length ≤ 15) {idxs : List Nat}
    {w a b : Nat} (hw : w < 6) (ha : a < 6) (hb : b < 6) :
    τV S idxs (.PW w a b) = true ↔ idxOf a (rowOrderW S w) < idxOf b (rowOrderW S w) := by
  unfold rowOrderW
  rw [rowOrder_lt_iff ha hb]
  have hWF := hL.1
  have hnd : (strajW S w).Nodup := hL.2.2 w hw
  have hmemA : a ∈ (strajW S w).reverse ↔ a ∈ colW S w := by
    rw [List.mem_reverse, strajW_eq_destutter_colW, mem_destutter_ne_iff]
  have hmemB : b ∈ (strajW S w).reverse ↔ b ∈ colW S w := by
    rw [List.mem_reverse, strajW_eq_destutter_colW, mem_destutter_ne_iff]
  have hfull : (colW S w).take 16 = colW S w :=
    List.take_of_length_le (by rw [colW_length]; omega)
  have hv15a : vis S 15 a w = true ↔ a ∈ colW S w := by
    rw [vis_iff_mem_take_colW hWF ha hw, hfull]
  have hv15b : vis S 15 b w = true ↔ b ∈ colW S w := by
    rw [vis_iff_mem_take_colW hWF hb hw, hfull]
  have hv15a' : vis S 15 a w = false ↔ a ∉ colW S w := by rw [Bool.eq_false_iff, ne_eq, hv15a]
  have hv15b' : vis S 15 b w = false ↔ b ∉ colW S w := by rw [Bool.eq_false_iff, ne_eq, hv15b]
  simp only [τV, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_iff]
  rw [befWB_iff hWF hlen hw hb ha, hv15a, hv15a', hv15b']
  by_cases hac : a ∈ colW S w <;> by_cases hbc : b ∈ colW S w
  · have had := hmemA.2 hac
    have hbd := hmemB.2 hbc
    have hdA : a ∈ strajW S w := List.mem_reverse.1 had
    have hdB : b ∈ strajW S w := List.mem_reverse.1 hbd
    have hrev := idxOf_reverse_lt_iff hnd hdA hdB
    have hd := idxOf_destutter_lt_iff hbc hac
    rw [← strajW_eq_destutter_colW] at hd
    simp [hac, hbc, had, hbd, hrev, hd]
  · have had := hmemA.2 hac
    have hbd : b ∉ (strajW S w).reverse := fun h => hbc (hmemB.1 h)
    simp [hac, hbc, had, hbd]
  · have had : a ∉ (strajW S w).reverse := fun h => hac (hmemA.1 h)
    have hbd := hmemB.2 hbc
    simp [hac, hbc, had, hbd]
  · have had : a ∉ (strajW S w).reverse := fun h => hac (hmemA.1 h)
    have hbd : b ∉ (strajW S w).reverse := fun h => hbc (hmemB.1 h)
    simp [hac, hbc, had, hbd]
