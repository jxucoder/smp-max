import SmpMax.Five.Symmetry
import SmpMax.Five.Encoding
import Mathlib.Tactic.IntervalCases

/-!
# Faithfulness, part A: the assignment and literal-evaluation lemmas

Given an instance `I` and the sorted index list `idxs` of its stable
matchings (indices into `perms120`), `tau I idxs` is the assignment fed
to `cubeCNF`:
- preference variables read off `I`'s rank tables;
- selector variable (t, μi) is true iff `idxs.getD t 120 = μi`.
-/

def tau (I : Inst) (idxs : List Nat) : Nat → Bool := fun v =>
  if v ≤ 50 then
    let u := v - 1
    let ab := pairs5.getD (u % 10) (0, 0)
    decide (get2 I.mrank (u / 10) ab.1 < get2 I.mrank (u / 10) ab.2)
  else if v ≤ 100 then
    let u := v - 51
    let ab := pairs5.getD (u % 10) (0, 0)
    decide (get2 I.wrank (u / 10) ab.1 < get2 I.wrank (u / 10) ab.2)
  else
    let u := v - 101
    decide (idxs.getD (u / 120) 120 = u % 120)

/-! ## Arithmetic decode lemmas -/

theorem pidx_lt {a b : Nat} (hab : a < b) (hb : b < 5) : pidx a b < 10 := by
  interval_cases b <;> interval_cases a <;> decide

theorem pairs5_pidx {a b : Nat} (hab : a < b) (hb : b < 5) :
    pairs5.getD (pidx a b) (0, 0) = (a, b) := by
  interval_cases b <;> interval_cases a <;> rfl

theorem eval_prefVar_m {I : Inst} {idxs : List Nat} {i a b : Nat}
    (hi : i < 5) (hab : a < b) (hb : b < 5) :
    tau I idxs (prefVar 0 i a b) =
      decide (get2 I.mrank i a < get2 I.mrank i b) := by
  have hp : pidx a b < 10 := pidx_lt hab hb
  have hv : prefVar 0 i a b ≤ 50 := by
    simp only [prefVar]; omega
  have h1 : prefVar 0 i a b - 1 = i * 10 + pidx a b := by
    simp only [prefVar]; omega
  simp only [tau, if_pos hv, h1]
  have hdiv : (i * 10 + pidx a b) / 10 = i := by omega
  have hmod : (i * 10 + pidx a b) % 10 = pidx a b := by omega
  rw [hdiv, hmod, pairs5_pidx hab hb]

theorem eval_prefVar_w {I : Inst} {idxs : List Nat} {i a b : Nat}
    (hi : i < 5) (hab : a < b) (hb : b < 5) :
    tau I idxs (prefVar 1 i a b) =
      decide (get2 I.wrank i a < get2 I.wrank i b) := by
  have hp : pidx a b < 10 := pidx_lt hab hb
  have hv1 : ¬(prefVar 1 i a b ≤ 50) := by
    simp only [prefVar]; omega
  have hv2 : prefVar 1 i a b ≤ 100 := by
    simp only [prefVar]; omega
  have h1 : prefVar 1 i a b - 51 = i * 10 + pidx a b := by
    simp only [prefVar]; omega
  simp only [tau, if_neg hv1, if_pos hv2, h1]
  have hdiv : (i * 10 + pidx a b) / 10 = i := by omega
  have hmod : (i * 10 + pidx a b) % 10 = pidx a b := by omega
  rw [hdiv, hmod, pairs5_pidx hab hb]

/-- Rank values within one well-formed row are injective below 5. -/
theorem rank_inj {t : List (List Nat)} {i a b : Nat}
    (hrow : isRankRow (t.getD i []) = true)
    (ha : a < 5) (hb : b < 5)
    (heq : get2 t i a = get2 t i b) : a = b := by
  have hp : (t.getD i []).Perm idRow := rankRow_perm hrow
  have hnd : (t.getD i []).Nodup := sigma_nodup hp
  have hlen : (t.getD i []).length = 5 := sigma_length hp
  have h1 : idxOf (get2 t i a) (t.getD i []) = a :=
    idxOf_getD hnd (by rw [hlen]; exact ha)
  have h2 : idxOf (get2 t i b) (t.getD i []) = b :=
    idxOf_getD hnd (by rw [hlen]; exact hb)
  rw [← h1, ← h2, heq]

/-- Well-formedness gives `rank_inj` for men's row `m`. -/
theorem rank_inj_m {I : Inst} (h : WF I = true) {m a b : Nat}
    (hm : m < 5) (ha : a < 5) (hb : b < 5)
    (heq : get2 I.mrank m a = get2 I.mrank m b) : a = b := by
  obtain ⟨hml, _, hrows, _⟩ := WF_unfold h
  refine rank_inj ?_ ha hb heq
  have hlt : m < I.mrank.length := by omega
  rw [List.getD_eq_getElem _ _ hlt]
  exact hrows _ (List.getElem_mem hlt)

theorem rank_inj_w {I : Inst} (h : WF I = true) {w a b : Nat}
    (hw : w < 5) (ha : a < 5) (hb : b < 5)
    (heq : get2 I.wrank w a = get2 I.wrank w b) : a = b := by
  obtain ⟨_, hwl, _, hrows⟩ := WF_unfold h
  refine rank_inj ?_ ha hb heq
  have hlt : w < I.wrank.length := by omega
  rw [List.getD_eq_getElem _ _ hlt]
  exact hrows _ (List.getElem_mem hlt)

/-- Evaluation of a men's preference literal, arbitrary argument order. -/
theorem eval_prefLit_m {I : Inst} {idxs : List Nat} (h : WF I = true)
    {m a b : Nat} (hm : m < 5) (ha : a < 5) (hb : b < 5) (hab : a ≠ b) :
    evalLit (tau I idxs) (prefLit 0 m a b) =
      decide (get2 I.mrank m a < get2 I.mrank m b) := by
  by_cases hlt : a < b
  · simp only [prefLit, if_pos hlt, evalLit]
    rw [if_pos (by simp only [prefVar]; omega)]
    rw [show ((prefVar 0 m a b : Int)).toNat = prefVar 0 m a b from rfl]
    exact eval_prefVar_m hm hlt hb
  · have hba : b < a := by omega
    simp only [prefLit, if_neg hlt, evalLit]
    rw [if_neg (by simp only [prefVar]; omega), neg_neg]
    rw [show ((prefVar 0 m b a : Int)).toNat = prefVar 0 m b a from rfl]
    rw [eval_prefVar_m hm hba ha]
    have hne : get2 I.mrank m a ≠ get2 I.mrank m b :=
      fun hc => hab (rank_inj_m h hm ha hb hc)
    have hiff : (get2 I.mrank m a < get2 I.mrank m b) ↔
        ¬(get2 I.mrank m b < get2 I.mrank m a) := by omega
    rw [decide_eq_decide.mpr hiff, decide_not]

/-- Evaluation of a women's preference literal, arbitrary argument order. -/
theorem eval_prefLit_w {I : Inst} {idxs : List Nat} (h : WF I = true)
    {w a b : Nat} (hw : w < 5) (ha : a < 5) (hb : b < 5) (hab : a ≠ b) :
    evalLit (tau I idxs) (prefLit 1 w a b) =
      decide (get2 I.wrank w a < get2 I.wrank w b) := by
  by_cases hlt : a < b
  · simp only [prefLit, if_pos hlt, evalLit]
    rw [if_pos (by simp only [prefVar]; omega)]
    rw [show ((prefVar 1 w a b : Int)).toNat = prefVar 1 w a b from rfl]
    exact eval_prefVar_w hw hlt hb
  · have hba : b < a := by omega
    simp only [prefLit, if_neg hlt, evalLit]
    rw [if_neg (by simp only [prefVar]; omega), neg_neg]
    rw [show ((prefVar 1 w b a : Int)).toNat = prefVar 1 w b a from rfl]
    rw [eval_prefVar_w hw hba ha]
    have hne : get2 I.wrank w a ≠ get2 I.wrank w b :=
      fun hc => hab (rank_inj_w h hw ha hb hc)
    have hiff : (get2 I.wrank w a < get2 I.wrank w b) ↔
        ¬(get2 I.wrank w b < get2 I.wrank w a) := by omega
    rw [decide_eq_decide.mpr hiff, decide_not]

/-- Evaluation of a selector literal. -/
theorem eval_yLit {I : Inst} {idxs : List Nat} {t μi : Nat} (hμ : μi < 120) :
    evalLit (tau I idxs) (yLit t μi) = decide (idxs.getD t 120 = μi) := by
  have hpos : (0 : Int) < yLit t μi := by simp only [yLit, yVar]; omega
  simp only [evalLit, if_pos hpos]
  have htoNat : (yLit t μi).toNat = 101 + t * 120 + μi := rfl
  rw [htoNat]
  have hv1 : ¬(101 + t * 120 + μi ≤ 50) := by omega
  have hv2 : ¬(101 + t * 120 + μi ≤ 100) := by omega
  simp only [tau, if_neg hv1, if_neg hv2]
  have h1 : 101 + t * 120 + μi - 101 = t * 120 + μi := by omega
  rw [h1]
  have hdiv : (t * 120 + μi) / 120 = t := by omega
  have hmod : (t * 120 + μi) % 120 = μi := by omega
  rw [hdiv, hmod]

/-- A negated selector literal. -/
theorem eval_yLit_neg {I : Inst} {idxs : List Nat} {t μi : Nat} (hμ : μi < 120) :
    evalLit (tau I idxs) (-(yLit t μi)) = !decide (idxs.getD t 120 = μi) := by
  have hneg : ¬((0 : Int) < -(yLit t μi)) := by simp only [yLit, yVar]; omega
  simp only [evalLit, if_neg hneg, neg_neg]
  have htoNat : (yLit t μi).toNat = 101 + t * 120 + μi := rfl
  rw [htoNat]
  have hv1 : ¬(101 + t * 120 + μi ≤ 50) := by omega
  have hv2 : ¬(101 + t * 120 + μi ≤ 100) := by omega
  simp only [tau, if_neg hv1, if_neg hv2]
  have h1 : 101 + t * 120 + μi - 101 = t * 120 + μi := by omega
  rw [h1]
  have hdiv : (t * 120 + μi) / 120 = t := by omega
  have hmod : (t * 120 + μi) % 120 = μi := by omega
  rw [hdiv, hmod]

/-! ## Part B: clause-family satisfaction -/

theorem evalLit_neg {τ : Nat → Bool} {l : Int} (h : l ≠ 0) :
    evalLit τ (-l) = !(evalLit τ l) := by
  simp only [evalLit]
  by_cases hp : 0 < l
  · rw [if_neg (by omega), if_pos hp, neg_neg]
  · rw [if_pos (by omega), if_neg hp, Bool.not_not]

theorem prefLit_ne_zero {side i a b : Nat} : prefLit side i a b ≠ 0 := by
  simp only [prefLit, prefVar]
  split <;> omega

theorem yLit_ne_zero {t μi : Nat} : yLit t μi ≠ 0 := by
  simp only [yLit, yVar]; omega

theorem triples5_bounds : ∀ x ∈ triples5,
    x.1 < x.2.1 ∧ x.2.1 < x.2.2 ∧ x.2.2 < 5 := by decide

theorem pairs5_bounds : ∀ x ∈ pairs5, x.1 < x.2 ∧ x.2 < 5 := by decide

theorem idRow_getD {x : Nat} (hx : x < 5) : idRow.getD x 0 = x := by
  interval_cases x <;> rfl

section Families

variable {I : Inst} {idxs : List Nat}

theorem trans_sat (h : WF I = true) :
    transClauses.all (evalClause (tau I idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [transClauses, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨side, hside, i, hi, x, hx, hc⟩ := hc
  obtain ⟨hab, hbc, hc5⟩ := triples5_bounds x hx
  obtain ⟨a, b, c'⟩ := x
  simp only at hab hbc hc5
  have ha5 : a < 5 := by omega
  have hb5 : b < 5 := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  interval_cases side
  · rcases hc with rfl | rfl <;>
    · simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true,
        evalLit_neg prefLit_ne_zero,
        eval_prefLit_m h hi ha5 hb5 (by omega),
        eval_prefLit_m h hi hb5 hc5 (by omega),
        eval_prefLit_m h hi ha5 hc5 (by omega),
        Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      omega
  · rcases hc with rfl | rfl <;>
    · simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
        Bool.or_eq_true,
        evalLit_neg prefLit_ne_zero,
        eval_prefLit_w h hi ha5 hb5 (by omega),
        eval_prefLit_w h hi hb5 hc5 (by omega),
        eval_prefLit_w h hi ha5 hc5 (by omega),
        Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      omega

theorem man0_sat (h : WF I = true) (h0 : I.mrank.getD 0 [] = idRow) :
    man0Units.all (evalClause (tau I idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [man0Units, List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨hab, hb5⟩ := pairs5_bounds x hx
  obtain ⟨a, b⟩ := x
  simp only at hab hb5
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
    eval_prefLit_m h (show (0:Nat) < 5 by omega) (show a < 5 by omega) hb5
      (show a ≠ b by omega)]
  have hga : get2 I.mrank 0 a = a := by
    simp only [get2, h0]; exact idRow_getD (by omega)
  have hgb : get2 I.mrank 0 b = b := by
    simp only [get2, h0]; exact idRow_getD hb5
  rw [hga, hgb]
  exact decide_eq_true hab

theorem man1_sat (h : WF I = true) {row : List Nat}
    (h1 : I.mrank.getD 1 [] = row) :
    (man1Units row).all (evalClause (tau I idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [man1Units, List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨hab, hb5⟩ := pairs5_bounds x hx
  obtain ⟨a, b⟩ := x
  simp only at hab hb5
  have hga : get2 I.mrank 1 a = row.getD a 0 := by simp only [get2, h1]
  have hgb : get2 I.mrank 1 b = row.getD b 0 := by simp only [get2, h1]
  by_cases hcond : row.getD a 0 < row.getD b 0
  · simp only [if_pos hcond, evalClause, List.any_cons, List.any_nil,
      Bool.or_false, eval_prefLit_m h (show (1:Nat) < 5 by omega)
        (show a < 5 by omega) hb5 (show a ≠ b by omega), hga, hgb]
    exact decide_eq_true hcond
  · simp only [if_neg hcond, evalClause, List.any_cons, List.any_nil,
      Bool.or_false, evalLit_neg prefLit_ne_zero,
      eval_prefLit_m h (show (1:Nat) < 5 by omega) (show a < 5 by omega) hb5
        (show a ≠ b by omega), hga, hgb]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    exact hcond

end Families

/-! ## Part B2: selector clause families -/

section Families2

variable {I : Inst} {idxs : List Nat}

theorem nonempty_sat (hlen : 17 ≤ idxs.length)
    (hmem : ∀ μi ∈ idxs, μi < 120) :
    (nonemptyClausesK 17).all (evalClause (tau I idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [nonemptyClausesK, List.mem_map, List.mem_range] at hc
  obtain ⟨t, ht, rfl⟩ := hc
  have htl : t < idxs.length := by omega
  have hselmem : idxs.getD t 120 ∈ idxs := by
    rw [List.getD_eq_getElem _ _ htl]
    exact List.getElem_mem htl
  have hsel120 : idxs.getD t 120 < 120 := hmem _ hselmem
  rw [evalClause, List.any_eq_true]
  refine ⟨yLit t (idxs.getD t 120), ?_, ?_⟩
  · exact List.mem_map.2 ⟨_, List.mem_range.2 hsel120, rfl⟩
  · rw [eval_yLit hsel120]
    exact decide_eq_true rfl

theorem ordering_sat (hlen : 17 ≤ idxs.length)
    (hpair : idxs.Pairwise (· < ·)) :
    (orderingClausesK 17).all (evalClause (tau I idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [orderingClausesK, List.mem_flatMap, List.mem_map,
    List.mem_range] at hc
  obtain ⟨t, ht, μi, hμi, μj, hμj, rfl⟩ := hc
  have e1 := eval_yLit_neg (I := I) (idxs := idxs) (t := t) (μi := μi) hμi
  have e2 := eval_yLit_neg (I := I) (idxs := idxs) (t := t + 1) (μi := μj)
    (show μj < 120 by omega)
  simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
    Bool.or_eq_true, e1, e2, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h1 : idxs.getD t 120 = μi
  · right
    intro h2
    have htl : t < idxs.length := by omega
    have ht1 : t + 1 < idxs.length := by omega
    have hmono : idxs.getD t 120 < idxs.getD (t + 1) 120 := by
      rw [List.getD_eq_getElem _ _ htl, List.getD_eq_getElem _ _ ht1]
      exact List.pairwise_iff_getElem.mp hpair t (t + 1) htl ht1 (by omega)
    omega
  · left; exact h1

theorem block_sat (h : WF I = true) (hlen : 17 ≤ idxs.length)
    (hstab : ∀ μi ∈ idxs, μi < 120 ∧ isStable I (perms120.getD μi []) = true) :
    (blockClausesK 17).all (evalClause (tau I idxs)) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp only [blockClausesK, List.mem_flatMap, List.mem_range,
    List.mem_filterMap] at hc
  obtain ⟨t, ht, μi, hμi, m, hm, w, hw, hite⟩ := hc
  by_cases hwm : w = (perms120.getD μi []).getD m 0
  · rw [if_pos hwm] at hite
    exact absurd hite (by simp)
  · rw [if_neg hwm] at hite
    obtain rfl := (Option.some.inj hite).symm
    have e1 := eval_yLit_neg (I := I) (idxs := idxs) (t := t) (μi := μi) hμi
    simp only [evalClause, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, e1, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases hy : idxs.getD t 120 = μi
    · -- slot t selects μi: the matching is stable, use a rank disjunct
      right
      have htl : t < idxs.length := by omega
      have hμmem : μi ∈ idxs := by
        rw [← hy, List.getD_eq_getElem _ _ htl]
        exact List.getElem_mem htl
      obtain ⟨hμ120, hstab'⟩ := hstab μi hμmem
      have hmuperm : (perms120.getD μi []).Perm idRow := by
        have hμlt : μi < perms120.length := by rw [perms120_length]; exact hμ120
        rw [List.getD_eq_getElem _ _ hμlt]
        exact List.mem_permutations.1 (List.getElem_mem hμlt)
      have hwm5 : (perms120.getD μi []).getD m 0 < 5 :=
        sigma_app_lt hmuperm hm
      have hwmem : w ∈ perms120.getD μi [] := sigma_mem hmuperm hw
      have hmw5 : idxOf w (perms120.getD μi []) < 5 := by
        have := idxOf_lt_length hwmem
        rw [sigma_length hmuperm] at this
        exact this
      have hmneq : m ≠ idxOf w (perms120.getD μi []) := by
        intro he
        apply hwm
        rw [he]
        exact (getD_idxOf hwmem).symm
      have e2 := eval_prefLit_m (idxs := idxs) h hm hw hwm5 hwm
      have e3 := eval_prefLit_w (idxs := idxs) h hw hm hmw5 hmneq
      simp only [evalLit_neg prefLit_ne_zero, e2, e3,
        Bool.not_eq_true', decide_eq_false_iff_not]
      -- extract the (m, w) case of stability
      simp only [isStable, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_true_eq, decide_eq_false_iff_not] at hstab'
      have hbody := hstab' m hm w hw
      rcases hbody with heq | hdisj
      · exact absurd heq hwm
      · exact hdisj
    · left; exact hy

end Families2

/-! ## Part C: the index list and the faithfulness theorem -/

theorem map_getD_range_len {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_map, List.getElem_range,
      List.getElem?_eq_getElem h2, List.getD_eq_getElem _ _ h2]

theorem filter_range_length {α : Type} (l : List α) (p : α → Bool) (d : α) :
    ((List.range l.length).filter (fun i => p (l.getD i d))).length
      = (l.filter p).length := by
  conv_rhs => rw [← map_getD_range_len l d]
  rw [List.filter_map, List.length_map]
  rfl

/-- **Faithfulness**: a well-formed instance with man 0 ranking
identically, man 1's rank row `row`, and ≥ 17 stable matchings yields a
satisfying assignment of `cubeCNF row`. -/
theorem cube_faithful' {I : Inst} (h : WF I = true)
    (h0 : I.mrank.getD 0 [] = idRow) {row : List Nat}
    (h1 : I.mrank.getD 1 [] = row)
    (hcnt : 17 ≤ stableCount I) :
    Satisfiable (cubeCNF row) := by
  set idxs := (List.range 120).filter
    (fun μi => isStable I (perms120.getD μi [])) with hidxs
  have hcount : idxs.length = stableCount I := by
    rw [hidxs, show (120 : Nat) = perms120.length from perms120_length.symm,
      filter_range_length perms120 (isStable I) []]
    rfl
  have hlen : 17 ≤ idxs.length := by omega
  have hpair : idxs.Pairwise (· < ·) := by
    rw [hidxs]
    exact (List.pairwise_lt_range).filter _
  have hstab : ∀ μi ∈ idxs,
      μi < 120 ∧ isStable I (perms120.getD μi []) = true := by
    intro μi hmem
    rw [hidxs, List.mem_filter, List.mem_range] at hmem
    exact ⟨hmem.1, hmem.2⟩
  refine ⟨tau I idxs, ?_⟩
  rw [show cubeCNF row = transClauses ++ man0Units ++ man1Units row ++
      nonemptyClausesK 17 ++ orderingClausesK 17 ++ blockClausesK 17 from rfl]
  simp only [evalCNF, List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨trans_sat h, man0_sat h h0⟩, man1_sat h h1⟩,
    nonempty_sat hlen (fun μi hm => (hstab μi hm).1)⟩,
    ordering_sat hlen hpair⟩, block_sat h hlen hstab⟩
