import SmpMax.Five.Symmetry

/-!
# Order six: definitions and the bridge lemma (rotation-free)

For an order-6 instance `I`, `readoff I` promotes each person's stable
partners to the top of their list, preserving relative order. The
**bridge lemma** states `stableCount6 I ≤ stableCount6 (readoff I)`:
every stable matching of `I` remains stable in `readoff I`. No rotation
theory is required.
-/

def idRow6 : List Nat := [0, 1, 2, 3, 4, 5]

structure Inst6 where
  mrank : List (List Nat)
  wrank : List (List Nat)
deriving Repr

def isRankRow6 (r : List Nat) : Bool :=
  r.length = 6 && (List.range 6).all fun v => r.contains v

def WF6 (I : Inst6) : Bool :=
  I.mrank.length = 6 && I.wrank.length = 6 &&
  I.mrank.all isRankRow6 && I.wrank.all isRankRow6

def isStable6 (I : Inst6) (mu : List Nat) : Bool :=
  (List.range 6).all fun m =>
    (List.range 6).all fun w =>
      let wm := mu.getD m 0
      let mw := idxOf w mu
      (w = wm) ||
      !(get2 I.mrank m w < get2 I.mrank m wm &&
        get2 I.wrank w m < get2 I.wrank w mw)

def sms6 (I : Inst6) : List (List Nat) :=
  idRow6.permutations.filter (isStable6 I)

def stableCount6 (I : Inst6) : Nat := (sms6 I).length

/-- `(m, w)` is a stable pair of `I`. -/
def stab (I : Inst6) (m w : Nat) : Bool :=
  (sms6 I).any fun mu => mu.getD m 0 == w

/-- Rank in the promoted list: elements satisfying `p` first (in original
relative order), then the rest (in original relative order). -/
def promoteRank (row : List Nat) (p : Nat → Bool) (x : Nat) : Nat :=
  if p x then
    ((List.range 6).filter fun y =>
      p y && decide (row.getD y 0 < row.getD x 0)).length
  else
    ((List.range 6).filter p).length +
    ((List.range 6).filter fun y =>
      !p y && decide (row.getD y 0 < row.getD x 0)).length

def readoff (I : Inst6) : Inst6 where
  mrank := (List.range 6).map fun m =>
    (List.range 6).map fun w => promoteRank (I.mrank.getD m []) (stab I m) w
  wrank := (List.range 6).map fun w =>
    (List.range 6).map fun m =>
      promoteRank (I.wrank.getD w []) (fun m' => stab I m' w) m

/-! ## Basic facts -/

theorem mem_sms6_perm {I : Inst6} {mu : List Nat} (h : mu ∈ sms6 I) :
    mu.Perm idRow6 :=
  List.mem_permutations.1 (List.mem_filter.1 h).1

theorem mem_sms6_stable {I : Inst6} {mu : List Nat} (h : mu ∈ sms6 I) :
    isStable6 I mu = true := (List.mem_filter.1 h).2

theorem perm6_length {mu : List Nat} (hp : mu.Perm idRow6) : mu.length = 6 := by
  have := hp.length_eq; simpa [idRow6] using this

theorem perm6_entry_lt {mu : List Nat} (hp : mu.Perm idRow6) {y : Nat}
    (hy : y ∈ mu) : y < 6 := by
  have : y ∈ idRow6 := hp.mem_iff.1 hy
  simp only [idRow6, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

theorem perm6_mem {mu : List Nat} (hp : mu.Perm idRow6) {v : Nat} (hv : v < 6) :
    v ∈ mu := by
  rw [hp.mem_iff]
  simp only [idRow6, List.mem_cons]
  omega

theorem perm6_getD_lt {mu : List Nat} (hp : mu.Perm idRow6) {m : Nat}
    (hm : m < 6) : mu.getD m 0 < 6 := by
  have hlt : m < mu.length := by rw [perm6_length hp]; exact hm
  refine perm6_entry_lt hp ?_
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

theorem stab_of_mem {I : Inst6} {mu : List Nat} (h : mu ∈ sms6 I) {m : Nat} :
    stab I m (mu.getD m 0) = true := by
  simp only [stab, List.any_eq_true]
  exact ⟨mu, h, by simp⟩

theorem stab_of_mem_w {I : Inst6} {mu : List Nat} (h : mu ∈ sms6 I) {w : Nat}
    (hw : w < 6) : stab I (idxOf w mu) w = true := by
  have hp := mem_sms6_perm h
  have hwmem : w ∈ mu := perm6_mem hp hw
  simp only [stab, List.any_eq_true]
  exact ⟨mu, h, by rw [getD_idxOf hwmem]; simp⟩

/-- Rank injectivity from well-formedness (order-6 version). -/
theorem rankRow6_perm {r : List Nat} (h : isRankRow6 r = true) :
    r.Perm idRow6 := by
  simp only [isRankRow6, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hmem⟩ := h
  have hsub : idRow6 ⊆ r := by
    intro v hv
    have hv6 : v < 6 := by
      simp only [idRow6, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
    have := hmem v hv6
    simpa [List.contains_iff_mem] using this
  have hnd : idRow6.Nodup := by decide
  have hsp : idRow6.Subperm r := hnd.subperm hsub
  have hlen' : r.length ≤ idRow6.length := by simp [hlen, idRow6]
  exact (hsp.perm_of_length_le hlen').symm

theorem rank_inj6 {t : List (List Nat)} {i a b : Nat} (hlen : t.length = 6)
    (hrows : ∀ r ∈ t, isRankRow6 r = true)
    (hi : i < 6) (ha : a < 6) (hb : b < 6)
    (heq : get2 t i a = get2 t i b) : a = b := by
  have hilt : i < t.length := by omega
  have hrow : isRankRow6 (t.getD i []) = true := by
    rw [List.getD_eq_getElem _ _ hilt]
    exact hrows _ (List.getElem_mem hilt)
  have hpr : (t.getD i []).Perm idRow6 := rankRow6_perm hrow
  have hnd : (t.getD i []).Nodup := hpr.nodup_iff.2 (by decide)
  have hl : (t.getD i []).length = 6 := perm6_length hpr
  have h1 : idxOf (get2 t i a) (t.getD i []) = a :=
    idxOf_getD hnd (by rw [hl]; exact ha)
  have h2 : idxOf (get2 t i b) (t.getD i []) = b :=
    idxOf_getD hnd (by rw [hl]; exact hb)
  rw [← h1, ← h2, heq]

/-! ## Counting lemmas for `promoteRank` -/

theorem filter_split {l : List Nat} {q₁ q₂ : Nat → Bool}
    (h : ∀ a ∈ l, q₁ a = true → q₂ a = true) :
    (l.filter q₂).length =
      (l.filter q₁).length + (l.filter fun a => q₂ a && !q₁ a).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases h1 : q₁ a = true
    · have h2 : q₂ a = true := h a List.mem_cons_self h1
      rw [List.filter_cons_of_pos (by simp [h2]),
          List.filter_cons_of_pos (by simp [h1]),
          List.filter_cons_of_neg (by simp [h1])]
      simp only [List.length_cons, ih']
      omega
    · have h1' : q₁ a = false := by simpa using h1
      by_cases h2 : q₂ a = true
      · rw [List.filter_cons_of_pos (by simp [h2]),
            List.filter_cons_of_neg (by simp [h1']),
            List.filter_cons_of_pos (by simp [h1', h2])]
        simp only [List.length_cons, ih']
        omega
      · have h2' : q₂ a = false := by simpa using h2
        rw [List.filter_cons_of_neg (by simp [h2']),
            List.filter_cons_of_neg (by simp [h1']),
            List.filter_cons_of_neg (by simp [h2'])]
        exact ih'

/-- If `rank x < rank y` (both promoted), then `promoteRank x < promoteRank y`. -/
theorem promoteRank_strict {row : List Nat} {p : Nat → Bool} {x y : Nat}
    (hx : p x = true) (hy : p y = true) (hx6 : x < 6)
    (hlt : row.getD x 0 < row.getD y 0) :
    promoteRank row p x < promoteRank row p y := by
  simp only [promoteRank, if_pos hx, if_pos hy]
  have hsplit : ((List.range 6).filter fun a =>
        p a && decide (row.getD a 0 < row.getD y 0)).length =
      ((List.range 6).filter fun a =>
        p a && decide (row.getD a 0 < row.getD x 0)).length +
      ((List.range 6).filter fun a =>
        (p a && decide (row.getD a 0 < row.getD y 0)) &&
        !(p a && decide (row.getD a 0 < row.getD x 0))).length :=
    filter_split (fun a _ ha => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ha ⊢
      exact ⟨ha.1, by omega⟩)
  have hwit : 0 < ((List.range 6).filter fun a =>
      (p a && decide (row.getD a 0 < row.getD y 0)) &&
      !(p a && decide (row.getD a 0 < row.getD x 0))).length := by
    rw [List.length_pos_iff_exists_mem]
    refine ⟨x, List.mem_filter.2 ⟨by simpa using hx6, ?_⟩⟩
    have h1 : (p x && decide (row.getD x 0 < row.getD y 0)) = true := by
      rw [hx]; simpa using hlt
    have h2 : (p x && decide (row.getD x 0 < row.getD x 0)) = false := by simp
    rw [h1, h2]
    rfl
  omega

/-- A promoted element ranks strictly above every non-promoted one. -/
theorem promoteRank_promoted_lt {row : List Nat} {p : Nat → Bool} {x y : Nat}
    (hx : p x = true) (hy : p y = false) (hx6 : x < 6) :
    promoteRank row p x < promoteRank row p y := by
  have hyneg : ¬(p y = true) := by intro hc; rw [hy] at hc; cases hc
  simp only [promoteRank, if_pos hx, if_neg hyneg]
  have hsplit : ((List.range 6).filter p).length =
      ((List.range 6).filter fun a =>
        p a && decide (row.getD a 0 < row.getD x 0)).length +
      ((List.range 6).filter fun a =>
        p a && !(p a && decide (row.getD a 0 < row.getD x 0))).length :=
    filter_split (fun a _ ha => by
      simp only [Bool.and_eq_true] at ha
      exact ha.1)
  have hwit : 0 < ((List.range 6).filter fun a =>
      p a && !(p a && decide (row.getD a 0 < row.getD x 0))).length := by
    rw [List.length_pos_iff_exists_mem]
    refine ⟨x, List.mem_filter.2 ⟨by simpa using hx6, ?_⟩⟩
    simp [hx]
  omega

theorem getD_map_range6 {α : Type} {d : α} {f : Nat → α} {w : Nat}
    (hw : w < 6) : ((List.range 6).map f).getD w d = f w := by
  have hlt : w < ((List.range 6).map f).length := by simpa using hw
  rw [List.getD_eq_getElem _ _ hlt]
  simp

/-! ## The bridge lemma -/

theorem readoff_mrank {I : Inst6} {m x : Nat} (hm : m < 6) (hx : x < 6) :
    get2 (readoff I).mrank m x =
      promoteRank (I.mrank.getD m []) (stab I m) x := by
  simp only [get2, readoff]
  rw [getD_map_range6 (d := ([] : List Nat)) hm, getD_map_range6 hx]

theorem readoff_wrank {I : Inst6} {w x : Nat} (hw : w < 6) (hx : x < 6) :
    get2 (readoff I).wrank w x =
      promoteRank (I.wrank.getD w []) (fun m' => stab I m' w) x := by
  simp only [get2, readoff]
  rw [getD_map_range6 (d := ([] : List Nat)) hw, getD_map_range6 hx]

theorem bridge_stable {I : Inst6} (h : WF6 I = true) {mu : List Nat}
    (hmu : mu ∈ sms6 I) : isStable6 (readoff I) mu = true := by
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hml, hwl⟩, hmrows⟩, hwrows⟩ := h
  have hp := mem_sms6_perm hmu
  have hst := mem_sms6_stable hmu
  simp only [isStable6, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not] at hst ⊢
  intro m hm w hw
  by_cases heq : w = mu.getD m 0
  · exact Or.inl heq
  · right
    have hwm6 : mu.getD m 0 < 6 := perm6_getD_lt hp hm
    have hmw6 : idxOf w mu < 6 := by
      have hwmem : w ∈ mu := perm6_mem hp hw
      have := idxOf_lt_length hwmem
      rw [perm6_length hp] at this
      exact this
    have hstwm : stab I m (mu.getD m 0) = true := stab_of_mem hmu
    have hstmw : stab I (idxOf w mu) w = true := stab_of_mem_w hmu hw
    have hmne : m ≠ idxOf w mu := by
      intro he
      apply heq
      have hwmem : w ∈ mu := perm6_mem hp hw
      rw [he]
      exact (getD_idxOf hwmem).symm
    rw [readoff_mrank hm hw, readoff_mrank hm hwm6,
        readoff_wrank hw hm, readoff_wrank hw hmw6]
    by_cases hsw : stab I m w
    · have hbody := hst m hm w hw
      rcases hbody with h1 | h2 | h2
      · exact absurd h1 heq
      · -- man side: I does not prefer, so readoff does not prefer
        left
        intro hcon
        have hne : get2 I.mrank m w ≠ get2 I.mrank m (mu.getD m 0) :=
          fun hc => heq (rank_inj6 hml hmrows hm hw hwm6 hc)
        have hlt' : (I.mrank.getD m []).getD (mu.getD m 0) 0 <
            (I.mrank.getD m []).getD w 0 := by
          simp only [get2] at h2 hne
          omega
        have := promoteRank_strict hstwm hsw hwm6 hlt'
        omega
      · -- woman side
        right
        intro hcon
        have hne : get2 I.wrank w m ≠ get2 I.wrank w (idxOf w mu) :=
          fun hc => hmne (rank_inj6 hwl hwrows hw hm hmw6 hc)
        have hlt' : (I.wrank.getD w []).getD (idxOf w mu) 0 <
            (I.wrank.getD w []).getD m 0 := by
          simp only [get2] at h2 hne
          omega
        have := promoteRank_strict (p := fun m' => stab I m' w)
          hstmw hsw hmw6 hlt'
        omega
    · -- w is not a stable partner of m: m cannot prefer w in readoff
      left
      intro hcon
      have hsw' : stab I m w = false := by simpa using hsw
      have := promoteRank_promoted_lt (row := I.mrank.getD m [])
        hstwm hsw' hwm6
      omega

theorem filter_sublist_of_imp {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = true → q a = true) :
    List.Sublist (l.filter p) (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons a t ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    by_cases hpa : p a = true
    · have hqa : q a = true := h a List.mem_cons_self hpa
      simpa [List.filter_cons, hpa, hqa] using ih'.cons₂ a
    · have hpa' : p a = false := by simpa using hpa
      by_cases hqa : q a = true
      · simpa [List.filter_cons, hpa', hqa] using ih'.cons a
      · have hqa' : q a = false := by simpa using hqa
        simpa [List.filter_cons, hpa', hqa'] using ih'

theorem bridge (I : Inst6) (h : WF6 I = true) :
    stableCount6 I ≤ stableCount6 (readoff I) := by
  unfold stableCount6 sms6
  refine (filter_sublist_of_imp ?_).length_le
  intro mu hmul hst
  exact bridge_stable h (List.mem_filter.2 ⟨hmul, hst⟩)
