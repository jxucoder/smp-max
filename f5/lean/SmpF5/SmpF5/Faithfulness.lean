import SmpF5.Symmetry
import SmpF5.Encoding
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
