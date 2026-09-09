import SmpMax.Six.ScheduleEncoding
import Mathlib.Tactic.IntervalCases

/-!
# Decoding variable ids of the order-6 schedule CNF

`SchedCNF6` numbers variables in the Python allocator's order with
explicit per-block offset functions.  `dec6 k v` inverts that numbering
(the f(5) `tau` pattern: range tests, then `/` and `%`), so that an
assignment can be defined by cases on the decoded variable.  The twelve
decode lemmas `dec_*` say that decoding an offset function's value gives
back its arguments (docs/design/f6-faithfulness.md §4.1, L4.1–L4.3).
-/

namespace SchedCNF6

/-! ## L4.1: the order-6 layout evaluates to `⟨6, 15, 409, 720⟩` -/

set_option maxRecDepth 4000 in
theorem cyclicShapes6_length : (cyclicShapes 6).length = 409 := by decide

set_option maxRecDepth 4000 in
theorem permsN6_length : (permsN 6).length = 720 := by decide

theorem layout6_eq : layout 6 = ⟨6, 15, 409, 720⟩ := by
  unfold layout
  rw [cyclicShapes6_length, permsN6_length]

theorem pwPerW6 : pwPerW 6 = 105 := by decide

/-! ## The offset functions at order 6, as closed forms -/

theorem mVar6 (t m w : Nat) : mVar (layout 6) t m w = 1 + 36 * t + 6 * m + w := by
  simp only [mVar, layout6_eq]; omega

theorem vVar6 (t m w : Nat) : vVar (layout 6) t m w = 577 + 36 * t + 6 * m + w := by
  simp only [vVar, layout6_eq]; omega

theorem sVar6 (t j : Nat) : sVar (layout 6) t j = 1153 + 410 * t + j := by
  simp only [sVar, sBase, layout6_eq]; omega

theorem cVar6 (m a b t : Nat) :
    cVar (layout 6) m a b t = 7303 + 17 * (30 * m + opIdx 6 a b) + t := by
  simp only [cVar, beforeBase, sBase, layout6_eq]; omega

theorem beforeVar6 (m a b : Nat) :
    beforeVar (layout 6) m a b = 7303 + 17 * (30 * m + opIdx 6 a b) + 16 := by
  simp only [beforeVar, layout6_eq, cVar, beforeBase, sBase]; omega

theorem neitherVar6 (m a b : Nat) :
    neitherVar (layout 6) m a b = 10363 + 15 * m + upIdx 6 a b := by
  simp only [neitherVar, neitherBase, beforeBase, sBase, layout6_eq]; omega

theorem pmVar6 (m a b : Nat) : pmVar (layout 6) m a b = 10453 + 30 * m + opIdx 6 a b := by
  simp only [pmVar, pmBase, neitherBase, beforeBase, sBase, layout6_eq]; omega

theorem cWVar6 (w a b t : Nat) :
    cWVar (layout 6) w a b t = 10633 + 17 * (30 * w + opIdx 6 a b) + t := by
  simp only [cWVar, beforeWBase, pmBase, neitherBase, beforeBase, sBase, layout6_eq]; omega

theorem beforeWVar6 (w a b : Nat) :
    beforeWVar (layout 6) w a b = 10633 + 17 * (30 * w + opIdx 6 a b) + 16 := by
  simp only [beforeWVar, cWVar, beforeWBase, pmBase, neitherBase, beforeBase, sBase,
    layout6_eq]; omega

theorem pwVar6 (w a b i : Nat) :
    pwVar (layout 6) w a b i = 13693 + 105 * w + pwOff 6 a b + i := by
  simp only [pwVar, pwBase, beforeWBase, pmBase, neitherBase, beforeBase, sBase, layout6_eq,
    pwPerW6]; omega

theorem yVar6 (t i : Nat) : yVar (layout 6) t i = 14323 + 720 * t + i := by
  simp only [yVar, yBase, pwBase, beforeWBase, pmBase, neitherBase, beforeBase, sBase,
    layout6_eq, pwPerW6]; omega

theorem pfVar6 (k t i : Nat) : pfVar (layout 6) k t i = 14323 + 720 * k + 720 * t + i := by
  simp only [pfVar, yBase, pwBase, beforeWBase, pmBase, neitherBase, beforeBase, sBase,
    layout6_eq, pwPerW6]; omega

/-! ## L4.2: inverse tables for the pair indices -/

/-- The unordered pairs `(a, b)`, `a < b`, in Python loop order. -/
def upairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a =>
    (List.range n).filterMap fun b => if a < b then some (a, b) else none

/-- `(a, b, i)` in `pwVar` id order within one woman (length 105). -/
def pwTable : List (Nat × Nat × Nat) :=
  (opairs 6).flatMap fun ab => (List.range (pwWidth ab.1 ab.2)).map fun i => (ab.1, ab.2, i)

theorem opIdx_lt {a b : Nat} (hab : a ≠ b) (ha : a < 6) (hb : b < 6) : opIdx 6 a b < 30 := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | decide

theorem opairs_getD_opIdx {a b : Nat} (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    (opairs 6).getD (opIdx 6 a b) (0, 0) = (a, b) := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | decide

theorem upIdx_lt {a b : Nat} (hab : a < b) (hb : b < 6) : upIdx 6 a b < 15 := by
  interval_cases b <;> interval_cases a <;> decide

theorem upairs_getD_upIdx {a b : Nat} (hab : a < b) (hb : b < 6) :
    (upairs 6).getD (upIdx 6 a b) (0, 0) = (a, b) := by
  interval_cases b <;> interval_cases a <;> decide

theorem pwWidth_le (a b : Nat) : pwWidth a b ≤ 4 := by
  unfold pwWidth; split <;> omega

theorem pwOff_add_lt {a b i : Nat} (hab : a ≠ b) (ha : a < 6) (hb : b < 6)
    (hi : i < pwWidth a b) : pwOff 6 a b + i < 105 := by
  have hi4 : i < 4 := lt_of_lt_of_le hi (pwWidth_le a b)
  interval_cases a <;> interval_cases b <;> interval_cases i <;>
    first | exact absurd rfl hab | decide | (exfalso; simp [pwWidth] at hi)

theorem pwTable_getD {a b i : Nat} (hab : a ≠ b) (ha : a < 6) (hb : b < 6)
    (hi : i < pwWidth a b) : pwTable.getD (pwOff 6 a b + i) (0, 0, 0) = (a, b, i) := by
  have hi4 : i < 4 := lt_of_lt_of_le hi (pwWidth_le a b)
  interval_cases a <;> interval_cases b <;> interval_cases i <;>
    first | exact absurd rfl hab | decide | (exfalso; simp [pwWidth] at hi)

/-! ## The decoded variable and the decoder -/

inductive V6
  | M (t m w : Nat) | Vis (t m w : Nat) | St (t j : Nat)
  | C (m a b t : Nat) | Bef (m a b : Nat) | Nei (m a b : Nat) | PM (m a b : Nat)
  | CW (w a b t : Nat) | BefW (w a b : Nat)
  | PW (w a b : Nat) | Later (w a b : Nat) | OnlyA (w a b : Nat) | NeiW (w a b : Nat)
  | Y (t i : Nat) | Pf (t i : Nat) | junk
deriving Repr, DecidableEq

def dec6 (k : Nat) (v : Nat) : V6 :=
  if v = 0 then .junk
  else if v ≤ 576 then
    let u := v - 1
    .M (u / 36) (u % 36 / 6) (u % 6)
  else if v ≤ 1152 then
    let u := v - 577
    .Vis (u / 36) (u % 36 / 6) (u % 6)
  else if v ≤ 7302 then
    let u := v - 1153
    .St (u / 410) (u % 410)
  else if v ≤ 10362 then
    let u := v - 7303
    let g := u / 17
    let ab := (opairs 6).getD (g % 30) (0, 0)
    if u % 17 = 16 then .Bef (g / 30) ab.1 ab.2 else .C (g / 30) ab.1 ab.2 (u % 17)
  else if v ≤ 10452 then
    let u := v - 10363
    let ab := (upairs 6).getD (u % 15) (0, 0)
    .Nei (u / 15) ab.1 ab.2
  else if v ≤ 10632 then
    let u := v - 10453
    let ab := (opairs 6).getD (u % 30) (0, 0)
    .PM (u / 30) ab.1 ab.2
  else if v ≤ 13692 then
    let u := v - 10633
    let g := u / 17
    let ab := (opairs 6).getD (g % 30) (0, 0)
    if u % 17 = 16 then .BefW (g / 30) ab.1 ab.2 else .CW (g / 30) ab.1 ab.2 (u % 17)
  else if v ≤ 14322 then
    let u := v - 13693
    let abi := pwTable.getD (u % 105) (0, 0, 0)
    match abi.2.2 with
    | 0 => .PW (u / 105) abi.1 abi.2.1
    | 1 => .Later (u / 105) abi.1 abi.2.1
    | 2 => .OnlyA (u / 105) abi.1 abi.2.1
    | _ => .NeiW (u / 105) abi.1 abi.2.1
  else if v ≤ 14322 + 720 * k then
    let u := v - 14323
    .Y (u / 720) (u % 720)
  else if v ≤ 14322 + 1440 * k then
    let u := v - 14323 - 720 * k
    .Pf (u / 720) (u % 720)
  else .junk

/-! ## L4.3: the twelve decode lemmas -/

theorem dec_mVar {k t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    dec6 k (mVar (layout 6) t m w) = .M t m w := by
  rw [mVar6]
  have h0 : ¬ (1 + 36 * t + 6 * m + w = 0) := by omega
  have h1 : 1 + 36 * t + 6 * m + w ≤ 576 := by omega
  simp only [dec6, if_neg h0, if_pos h1]
  have e1 : (1 + 36 * t + 6 * m + w - 1) / 36 = t := by omega
  have e2 : (1 + 36 * t + 6 * m + w - 1) % 36 / 6 = m := by omega
  have e3 : (1 + 36 * t + 6 * m + w - 1) % 6 = w := by omega
  rw [e1, e2, e3]

theorem dec_vVar {k t m w : Nat} (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) :
    dec6 k (vVar (layout 6) t m w) = .Vis t m w := by
  rw [vVar6]
  have h0 : ¬ (577 + 36 * t + 6 * m + w = 0) := by omega
  have h1 : ¬ (577 + 36 * t + 6 * m + w ≤ 576) := by omega
  have h2 : 577 + 36 * t + 6 * m + w ≤ 1152 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_pos h2]
  have e1 : (577 + 36 * t + 6 * m + w - 577) / 36 = t := by omega
  have e2 : (577 + 36 * t + 6 * m + w - 577) % 36 / 6 = m := by omega
  have e3 : (577 + 36 * t + 6 * m + w - 577) % 6 = w := by omega
  rw [e1, e2, e3]

theorem dec_sVar {k t j : Nat} (ht : t < 15) (hj : j ≤ 409) :
    dec6 k (sVar (layout 6) t j) = .St t j := by
  rw [sVar6]
  have h0 : ¬ (1153 + 410 * t + j = 0) := by omega
  have h1 : ¬ (1153 + 410 * t + j ≤ 576) := by omega
  have h2 : ¬ (1153 + 410 * t + j ≤ 1152) := by omega
  have h3 : 1153 + 410 * t + j ≤ 7302 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
  have e1 : (1153 + 410 * t + j - 1153) / 410 = t := by omega
  have e2 : (1153 + 410 * t + j - 1153) % 410 = j := by omega
  rw [e1, e2]

theorem dec_cVar {k m a b t : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6)
    (ht : t ≤ 15) : dec6 k (cVar (layout 6) m a b t) = .C m a b t := by
  rw [cVar6]
  have hop := opIdx_lt hab ha hb
  have h0 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + t = 0) := by omega
  have h1 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + t ≤ 576) := by omega
  have h2 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + t ≤ 1152) := by omega
  have h3 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + t ≤ 7302) := by omega
  have h4 : 7303 + 17 * (30 * m + opIdx 6 a b) + t ≤ 10362 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  have e1 : (7303 + 17 * (30 * m + opIdx 6 a b) + t - 7303) / 17 = 30 * m + opIdx 6 a b := by
    omega
  have e2 : (7303 + 17 * (30 * m + opIdx 6 a b) + t - 7303) % 17 = t := by omega
  have e3 : (30 * m + opIdx 6 a b) % 30 = opIdx 6 a b := by omega
  have e4 : (30 * m + opIdx 6 a b) / 30 = m := by omega
  have e5 : ¬ (t = 16) := by omega
  simp only [e1, e2, e3, e4, if_neg e5, opairs_getD_opIdx hab ha hb]

theorem dec_beforeVar {k m a b : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    dec6 k (beforeVar (layout 6) m a b) = .Bef m a b := by
  rw [beforeVar6]
  have hop := opIdx_lt hab ha hb
  have h0 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + 16 = 0) := by omega
  have h1 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + 16 ≤ 576) := by omega
  have h2 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + 16 ≤ 1152) := by omega
  have h3 : ¬ (7303 + 17 * (30 * m + opIdx 6 a b) + 16 ≤ 7302) := by omega
  have h4 : 7303 + 17 * (30 * m + opIdx 6 a b) + 16 ≤ 10362 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  have e1 : (7303 + 17 * (30 * m + opIdx 6 a b) + 16 - 7303) / 17 = 30 * m + opIdx 6 a b := by
    omega
  have e2 : (7303 + 17 * (30 * m + opIdx 6 a b) + 16 - 7303) % 17 = 16 := by omega
  have e3 : (30 * m + opIdx 6 a b) % 30 = opIdx 6 a b := by omega
  have e4 : (30 * m + opIdx 6 a b) / 30 = m := by omega
  simp only [e1, e2, e3, e4, if_true, opairs_getD_opIdx hab ha hb]

theorem dec_neitherVar {k m a b : Nat} (hm : m < 6) (hab : a < b) (hb : b < 6) :
    dec6 k (neitherVar (layout 6) m a b) = .Nei m a b := by
  rw [neitherVar6]
  have hup := upIdx_lt hab hb
  have h0 : ¬ (10363 + 15 * m + upIdx 6 a b = 0) := by omega
  have h1 : ¬ (10363 + 15 * m + upIdx 6 a b ≤ 576) := by omega
  have h2 : ¬ (10363 + 15 * m + upIdx 6 a b ≤ 1152) := by omega
  have h3 : ¬ (10363 + 15 * m + upIdx 6 a b ≤ 7302) := by omega
  have h4 : ¬ (10363 + 15 * m + upIdx 6 a b ≤ 10362) := by omega
  have h5 : 10363 + 15 * m + upIdx 6 a b ≤ 10452 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
  have e1 : (10363 + 15 * m + upIdx 6 a b - 10363) % 15 = upIdx 6 a b := by omega
  have e2 : (10363 + 15 * m + upIdx 6 a b - 10363) / 15 = m := by omega
  simp only [e1, e2, upairs_getD_upIdx hab hb]

theorem dec_pmVar {k m a b : Nat} (hm : m < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    dec6 k (pmVar (layout 6) m a b) = .PM m a b := by
  rw [pmVar6]
  have hop := opIdx_lt hab ha hb
  have h0 : ¬ (10453 + 30 * m + opIdx 6 a b = 0) := by omega
  have h1 : ¬ (10453 + 30 * m + opIdx 6 a b ≤ 576) := by omega
  have h2 : ¬ (10453 + 30 * m + opIdx 6 a b ≤ 1152) := by omega
  have h3 : ¬ (10453 + 30 * m + opIdx 6 a b ≤ 7302) := by omega
  have h4 : ¬ (10453 + 30 * m + opIdx 6 a b ≤ 10362) := by omega
  have h5 : ¬ (10453 + 30 * m + opIdx 6 a b ≤ 10452) := by omega
  have h6 : 10453 + 30 * m + opIdx 6 a b ≤ 10632 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
  have e1 : (10453 + 30 * m + opIdx 6 a b - 10453) % 30 = opIdx 6 a b := by omega
  have e2 : (10453 + 30 * m + opIdx 6 a b - 10453) / 30 = m := by omega
  simp only [e1, e2, opairs_getD_opIdx hab ha hb]

theorem dec_cWVar {k w a b t : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6)
    (ht : t ≤ 15) : dec6 k (cWVar (layout 6) w a b t) = .CW w a b t := by
  rw [cWVar6]
  have hop := opIdx_lt hab ha hb
  have h0 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + t = 0) := by omega
  have h1 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + t ≤ 576) := by omega
  have h2 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + t ≤ 1152) := by omega
  have h3 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + t ≤ 7302) := by omega
  have h4 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + t ≤ 10362) := by omega
  have h5 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + t ≤ 10452) := by omega
  have h6 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + t ≤ 10632) := by omega
  have h7 : 10633 + 17 * (30 * w + opIdx 6 a b) + t ≤ 13692 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    if_pos h7]
  have e1 : (10633 + 17 * (30 * w + opIdx 6 a b) + t - 10633) / 17 = 30 * w + opIdx 6 a b := by
    omega
  have e2 : (10633 + 17 * (30 * w + opIdx 6 a b) + t - 10633) % 17 = t := by omega
  have e3 : (30 * w + opIdx 6 a b) % 30 = opIdx 6 a b := by omega
  have e4 : (30 * w + opIdx 6 a b) / 30 = w := by omega
  have e5 : ¬ (t = 16) := by omega
  simp only [e1, e2, e3, e4, if_neg e5, opairs_getD_opIdx hab ha hb]

theorem dec_beforeWVar {k w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    dec6 k (beforeWVar (layout 6) w a b) = .BefW w a b := by
  rw [beforeWVar6]
  have hop := opIdx_lt hab ha hb
  have h0 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + 16 = 0) := by omega
  have h1 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + 16 ≤ 576) := by omega
  have h2 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + 16 ≤ 1152) := by omega
  have h3 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + 16 ≤ 7302) := by omega
  have h4 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + 16 ≤ 10362) := by omega
  have h5 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + 16 ≤ 10452) := by omega
  have h6 : ¬ (10633 + 17 * (30 * w + opIdx 6 a b) + 16 ≤ 10632) := by omega
  have h7 : 10633 + 17 * (30 * w + opIdx 6 a b) + 16 ≤ 13692 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    if_pos h7]
  have e1 : (10633 + 17 * (30 * w + opIdx 6 a b) + 16 - 10633) / 17 = 30 * w + opIdx 6 a b := by
    omega
  have e2 : (10633 + 17 * (30 * w + opIdx 6 a b) + 16 - 10633) % 17 = 16 := by omega
  have e3 : (30 * w + opIdx 6 a b) % 30 = opIdx 6 a b := by omega
  have e4 : (30 * w + opIdx 6 a b) / 30 = w := by omega
  simp only [e1, e2, e3, e4, if_true, opairs_getD_opIdx hab ha hb]

/-- Common core of the four `pwVar` decode lemmas. -/
theorem dec_pwVar_aux {k w a b i : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6)
    (hi : i < pwWidth a b) :
    dec6 k (pwVar (layout 6) w a b i) =
      match i with
      | 0 => .PW w a b
      | 1 => .Later w a b
      | 2 => .OnlyA w a b
      | _ => .NeiW w a b := by
  rw [pwVar6]
  have hlt := pwOff_add_lt hab ha hb hi
  have h0 : ¬ (13693 + 105 * w + pwOff 6 a b + i = 0) := by omega
  have h1 : ¬ (13693 + 105 * w + pwOff 6 a b + i ≤ 576) := by omega
  have h2 : ¬ (13693 + 105 * w + pwOff 6 a b + i ≤ 1152) := by omega
  have h3 : ¬ (13693 + 105 * w + pwOff 6 a b + i ≤ 7302) := by omega
  have h4 : ¬ (13693 + 105 * w + pwOff 6 a b + i ≤ 10362) := by omega
  have h5 : ¬ (13693 + 105 * w + pwOff 6 a b + i ≤ 10452) := by omega
  have h6 : ¬ (13693 + 105 * w + pwOff 6 a b + i ≤ 10632) := by omega
  have h7 : ¬ (13693 + 105 * w + pwOff 6 a b + i ≤ 13692) := by omega
  have h8 : 13693 + 105 * w + pwOff 6 a b + i ≤ 14322 := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    if_neg h7, if_pos h8]
  have e1 : (13693 + 105 * w + pwOff 6 a b + i - 13693) % 105 = pwOff 6 a b + i := by omega
  have e2 : (13693 + 105 * w + pwOff 6 a b + i - 13693) / 105 = w := by omega
  simp only [e1, e2, pwTable_getD hab ha hb hi]
  rcases i with _ | _ | _ | _ <;> rfl

theorem dec_pwVar0 {k w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    dec6 k (pwVar (layout 6) w a b 0) = .PW w a b :=
  dec_pwVar_aux hw hab ha hb (by unfold pwWidth; split <;> omega)

theorem dec_pwVar1 {k w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    dec6 k (pwVar (layout 6) w a b 1) = .Later w a b :=
  dec_pwVar_aux hw hab ha hb (by unfold pwWidth; split <;> omega)

theorem dec_pwVar2 {k w a b : Nat} (hw : w < 6) (hab : a ≠ b) (ha : a < 6) (hb : b < 6) :
    dec6 k (pwVar (layout 6) w a b 2) = .OnlyA w a b :=
  dec_pwVar_aux hw hab ha hb (by unfold pwWidth; split <;> omega)

theorem dec_pwVar3 {k w a b : Nat} (hw : w < 6) (hab : a < b) (hb : b < 6) :
    dec6 k (pwVar (layout 6) w a b 3) = .NeiW w a b :=
  dec_pwVar_aux hw (Nat.ne_of_lt hab) (by omega) hb (by unfold pwWidth; rw [if_pos hab]; omega)

theorem dec_yVar {k t i : Nat} (ht : t < k) (hi : i < 720) :
    dec6 k (yVar (layout 6) t i) = .Y t i := by
  rw [yVar6]
  have h0 : ¬ (14323 + 720 * t + i = 0) := by omega
  have h1 : ¬ (14323 + 720 * t + i ≤ 576) := by omega
  have h2 : ¬ (14323 + 720 * t + i ≤ 1152) := by omega
  have h3 : ¬ (14323 + 720 * t + i ≤ 7302) := by omega
  have h4 : ¬ (14323 + 720 * t + i ≤ 10362) := by omega
  have h5 : ¬ (14323 + 720 * t + i ≤ 10452) := by omega
  have h6 : ¬ (14323 + 720 * t + i ≤ 10632) := by omega
  have h7 : ¬ (14323 + 720 * t + i ≤ 13692) := by omega
  have h8 : ¬ (14323 + 720 * t + i ≤ 14322) := by omega
  have h9 : 14323 + 720 * t + i ≤ 14322 + 720 * k := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    if_neg h7, if_neg h8, if_pos h9]
  have e1 : (14323 + 720 * t + i - 14323) / 720 = t := by omega
  have e2 : (14323 + 720 * t + i - 14323) % 720 = i := by omega
  rw [e1, e2]

theorem dec_pfVar {k t i : Nat} (ht : t < k) (hi : i < 720) :
    dec6 k (pfVar (layout 6) k t i) = .Pf t i := by
  rw [pfVar6]
  have h0 : ¬ (14323 + 720 * k + 720 * t + i = 0) := by omega
  have h1 : ¬ (14323 + 720 * k + 720 * t + i ≤ 576) := by omega
  have h2 : ¬ (14323 + 720 * k + 720 * t + i ≤ 1152) := by omega
  have h3 : ¬ (14323 + 720 * k + 720 * t + i ≤ 7302) := by omega
  have h4 : ¬ (14323 + 720 * k + 720 * t + i ≤ 10362) := by omega
  have h5 : ¬ (14323 + 720 * k + 720 * t + i ≤ 10452) := by omega
  have h6 : ¬ (14323 + 720 * k + 720 * t + i ≤ 10632) := by omega
  have h7 : ¬ (14323 + 720 * k + 720 * t + i ≤ 13692) := by omega
  have h8 : ¬ (14323 + 720 * k + 720 * t + i ≤ 14322) := by omega
  have h9 : ¬ (14323 + 720 * k + 720 * t + i ≤ 14322 + 720 * k) := by omega
  have h10 : 14323 + 720 * k + 720 * t + i ≤ 14322 + 1440 * k := by omega
  simp only [dec6, if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    if_neg h7, if_neg h8, if_neg h9, if_pos h10]
  have e1 : (14323 + 720 * k + 720 * t + i - 14323 - 720 * k) / 720 = t := by omega
  have e2 : (14323 + 720 * k + 720 * t + i - 14323 - 720 * k) % 720 = i := by omega
  rw [e1, e2]

end SchedCNF6
