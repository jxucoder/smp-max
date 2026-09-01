import SmpF5.Lattice6

/-!
# Maximal chains in the dominance order (L5 prep)

`theChain I` walks from `manOpt I` to `womanOpt I` by repeatedly moving
to the strict dominator of minimum rank-sum. Minimality of the rank-sum
makes every step a cover for free.
-/

def sumRank (I : Inst6) (mu : List Nat) : Nat :=
  ((List.range 6).map fun m => get2 I.mrank m (mu.getD m 0)).sum

/-- Strict dominance, decidably. -/
def strictDomB (I : Inst6) (μ ν : List Nat) : Bool :=
  ((List.range 6).all fun m =>
    decide (get2 I.mrank m (μ.getD m 0) ≤ get2 I.mrank m (ν.getD m 0))) &&
  !(μ == ν)

theorem strictDomB_iff {I : Inst6} {μ ν : List Nat} :
    strictDomB I μ ν = true ↔ (domLe I μ ν ∧ μ ≠ ν) := by
  simp only [strictDomB, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, domLe]

/-! ## Sum monotonicity -/

theorem map_sum_le {f g : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, f x ≤ g x) →
    (l.map f).sum ≤ (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

theorem map_sum_lt {f g : Nat → Nat} :
    ∀ {l : List Nat}, (∀ x ∈ l, f x ≤ g x) → (∃ x ∈ l, f x < g x) →
    (l.map f).sum < (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons a t ih =>
    intro h ⟨x, hx, hlt⟩
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h2 := map_sum_le fun y hy => h y (List.mem_cons_of_mem _ hy)
      omega
    · have h1 := h a List.mem_cons_self
      have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨x, hx', hlt⟩
      omega

theorem sumRank_le_of_domLe {I : Inst6} {μ ν : List Nat}
    (h : domLe I μ ν) : sumRank I μ ≤ sumRank I ν :=
  map_sum_le fun m hm => h m (by simpa using hm)

/-- Strict dominance strictly increases the rank-sum (uses rank
injectivity to find a strict coordinate). -/
theorem sumRank_lt_of_strict {I : Inst6} (hWF : WF6 I = true)
    {μ ν : List Nat} (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I)
    (hdom : domLe I μ ν) (hne : μ ≠ ν) : sumRank I μ < sumRank I ν := by
  refine map_sum_lt (fun m hm => hdom m (by simpa using hm)) ?_
  by_contra hall
  push_neg at hall
  apply hne
  refine dominance_antisymm hWF hμ hν hdom ?_
  intro m hm
  have := hall m (by simpa using hm)
  omega

/-- Pointwise `≤` with equal sums forces pointwise equality. -/
theorem domLe_eq_of_sum_eq {I : Inst6} (hWF : WF6 I = true)
    {μ ν : List Nat} (hμ : μ ∈ sms6 I) (hν : ν ∈ sms6 I)
    (hdom : domLe I μ ν) (hsum : sumRank I ν ≤ sumRank I μ) : μ = ν := by
  by_contra hne
  have := sumRank_lt_of_strict hWF hμ hν hdom hne
  omega

/-! ## Argmin by rank-sum -/

def pickMin (I : Inst6) (x : List Nat) (xs : List (List Nat)) : List Nat :=
  xs.foldl (fun acc y => if sumRank I y < sumRank I acc then y else acc) x

theorem pickMin_spec {I : Inst6} :
    ∀ (xs : List (List Nat)) (x : List Nat),
    (pickMin I x xs = x ∨ pickMin I x xs ∈ xs) ∧
    (sumRank I (pickMin I x xs) ≤ sumRank I x) ∧
    (∀ y ∈ xs, sumRank I (pickMin I x xs) ≤ sumRank I y) := by
  intro xs
  induction xs with
  | nil => intro x; exact ⟨Or.inl rfl, le_refl _, by simp⟩
  | cons a t ih =>
    intro x
    have hstep : pickMin I x (a :: t) =
        pickMin I (if sumRank I a < sumRank I x then a else x) t := rfl
    by_cases hc : sumRank I a < sumRank I x
    · rw [hstep, if_pos hc]
      obtain ⟨hmem, hle, hall⟩ := ih a
      refine ⟨?_, by omega, ?_⟩
      · rcases hmem with h | h
        · exact Or.inr (by rw [h]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy'
        · omega
        · exact hall y hy'
    · rw [hstep, if_neg hc]
      obtain ⟨hmem, hle, hall⟩ := ih x
      refine ⟨?_, hle, ?_⟩
      · rcases hmem with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · omega
      · exact hall y hy'

/-! ## The chain construction -/

def CoverStep (I : Inst6) (x y : List Nat) : Prop :=
  domLe I x y ∧ x ≠ y ∧
  ∀ τ ∈ sms6 I, domLe I x τ → domLe I τ y → τ = x ∨ τ = y

def cands (I : Inst6) (cur : List Nat) : List (List Nat) :=
  (sms6 I).filter (strictDomB I cur)

def chainFrom (I : Inst6) : Nat → List Nat → List (List Nat)
  | 0, cur => [cur]
  | fuel + 1, cur =>
    match cands I cur with
    | [] => [cur]
    | c :: cs => cur :: chainFrom I fuel (pickMin I c cs)

def theChain (I : Inst6) : List (List Nat) := chainFrom I 31 (manOpt I)

theorem rank_lt6 {I : Inst6} (hWF : WF6 I = true) {m x : Nat}
    (hm : m < 6) (hx : x < 6) : get2 I.mrank m x < 6 := by
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hWF
  obtain ⟨⟨⟨hml, _⟩, hmrows⟩, _⟩ := hWF
  have hmlt : m < I.mrank.length := by omega
  have hrow : isRankRow6 (I.mrank.getD m []) = true := by
    rw [List.getD_eq_getElem _ _ hmlt]
    exact hmrows _ (List.getElem_mem hmlt)
  have hpr := rankRow6_perm hrow
  have hxl : x < (I.mrank.getD m []).length := by
    rw [perm6_length hpr]; exact hx
  have hmem : get2 I.mrank m x ∈ I.mrank.getD m [] := by
    simp only [get2]
    rw [List.getD_eq_getElem _ _ hxl]
    exact List.getElem_mem hxl
  exact perm6_entry_lt hpr hmem

theorem sumRank_le_30 {I : Inst6} (hWF : WF6 I = true) {mu : List Nat}
    (hmu : mu ∈ sms6 I) : sumRank I mu ≤ 30 := by
  have hp := mem_sms6_perm hmu
  have : sumRank I mu ≤ ((List.range 6).map fun _ => 5).sum := by
    refine map_sum_le ?_
    intro x hx
    have hx6 : x < 6 := by simpa using hx
    have := rank_lt6 hWF hx6 (perm6_getD_lt hp hx6)
    omega
  simpa using this

theorem cands_mem {I : Inst6} {cur τ : List Nat} (h : τ ∈ cands I cur) :
    τ ∈ sms6 I ∧ domLe I cur τ ∧ cur ≠ τ := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  obtain ⟨h3, h4⟩ := strictDomB_iff.1 h2
  exact ⟨h1, h3, h4⟩

theorem cands_empty_iff {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ [])
    {cur : List Nat} (hcur : cur ∈ sms6 I) :
    cands I cur = [] → cur = womanOpt I := by
  intro hempty
  by_contra hneq
  obtain ⟨hWmem, hWdom⟩ := womanOpt_spec hWF hne
  have : womanOpt I ∈ cands I cur := by
    refine List.mem_filter.2 ⟨hWmem, strictDomB_iff.2 ⟨hWdom cur hcur, hneq⟩⟩
  rw [hempty] at this
  exact absurd this (List.not_mem_nil)

theorem chainFrom_head (I : Inst6) (fuel : Nat) (cur : List Nat) :
    (chainFrom I fuel cur).head? = some cur := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [chainFrom]
    cases cands I cur with
    | nil => rfl
    | cons c cs => rfl

theorem chainFrom_mem {I : Inst6} :
    ∀ (fuel : Nat) (cur : List Nat), cur ∈ sms6 I →
    ∀ x ∈ chainFrom I fuel cur, x ∈ sms6 I := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur hcur x hx
    simp only [chainFrom, List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx ▸ hcur
  | succ f ih =>
    intro cur hcur x hx
    simp only [chainFrom] at hx
    rcases hc : cands I cur with _ | ⟨c, cs⟩
    · rw [hc] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      exact hx ▸ hcur
    · rw [hc] at hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hcur
      · have hnext : pickMin I c cs ∈ sms6 I := by
          obtain ⟨hmem, _, _⟩ := pickMin_spec (I := I) cs c
          have : pickMin I c cs ∈ cands I cur := by
            rcases hmem with h | h
            · rw [h, hc]; exact List.mem_cons_self
            · rw [hc]; exact List.mem_cons_of_mem _ h
          exact (cands_mem this).1
        exact ih _ hnext x hx'

theorem chainFrom_succ_nil {I : Inst6} {f : Nat} {cur : List Nat}
    (hc : cands I cur = []) : chainFrom I (f + 1) cur = [cur] := by
  simp only [chainFrom, hc]

theorem chainFrom_succ_cons {I : Inst6} {f : Nat} {cur c : List Nat}
    {cs : List (List Nat)} (hc : cands I cur = c :: cs) :
    chainFrom I (f + 1) cur = cur :: chainFrom I f (pickMin I c cs) := by
  simp only [chainFrom, hc]

theorem chainFrom_cover {I : Inst6} (hWF : WF6 I = true) :
    ∀ (fuel : Nat) (cur : List Nat), cur ∈ sms6 I →
    List.Chain' (CoverStep I) (chainFrom I fuel cur) := by
  intro fuel
  induction fuel with
  | zero => intro cur _; exact List.IsChain.singleton _
  | succ f ih =>
    intro cur hcur
    rcases hc : cands I cur with _ | ⟨c, cs⟩
    · rw [chainFrom_succ_nil hc]
      exact List.IsChain.singleton _
    · rw [chainFrom_succ_cons hc]
      obtain ⟨hmem, hlec, hall⟩ := pickMin_spec (I := I) cs c
      have hnextc : pickMin I c cs ∈ cands I cur := by
        rcases hmem with h | h
        · rw [h, hc]; exact List.mem_cons_self
        · rw [hc]; exact List.mem_cons_of_mem _ h
      obtain ⟨hnmem, hndom, hnne⟩ := cands_mem hnextc
      have hminall : ∀ τ ∈ cands I cur,
          sumRank I (pickMin I c cs) ≤ sumRank I τ := by
        intro τ hτ
        rw [hc] at hτ
        rcases List.mem_cons.1 hτ with rfl | hτ'
        · exact hlec
        · exact hall τ hτ'
      have hcover : CoverStep I cur (pickMin I c cs) := by
        refine ⟨hndom, hnne, ?_⟩
        intro τ hτmem hτ1 hτ2
        by_cases hτcur : τ = cur
        · exact Or.inl hτcur
        · right
          have hτcand : τ ∈ cands I cur :=
            List.mem_filter.2 ⟨hτmem, strictDomB_iff.2 ⟨hτ1, fun h => hτcur h.symm⟩⟩
          exact domLe_eq_of_sum_eq hWF hτmem hnmem hτ2 (hminall τ hτcand)
      have hchain := ih _ hnmem
      rcases ht : chainFrom I f (pickMin I c cs) with _ | ⟨h, t⟩
      · have h2 := chainFrom_head I f (pickMin I c cs)
        rw [ht] at h2
        simp at h2
      · have hh : h = pickMin I c cs := by
          have h2 := chainFrom_head I f (pickMin I c cs)
          rw [ht] at h2
          simpa using h2
        subst hh
        rw [ht] at hchain
        exact List.IsChain.cons_cons hcover hchain

theorem chainFrom_last {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ []) :
    ∀ (fuel : Nat) (cur : List Nat), cur ∈ sms6 I →
    sumRank I (womanOpt I) ≤ sumRank I cur + fuel →
    (chainFrom I fuel cur).getLast? = some (womanOpt I) := by
  intro fuel
  induction fuel with
  | zero =>
    intro cur hcur hfuel
    obtain ⟨hWmem, hWdom⟩ := womanOpt_spec hWF hne
    have : cur = womanOpt I :=
      domLe_eq_of_sum_eq hWF hcur hWmem (hWdom cur hcur) (by omega)
    simp [chainFrom, this]
  | succ f ih =>
    intro cur hcur hfuel
    rcases hc : cands I cur with _ | ⟨c, cs⟩
    · rw [chainFrom_succ_nil hc]
      have := cands_empty_iff hWF hne hcur hc
      simp [this]
    · rw [chainFrom_succ_cons hc]
      obtain ⟨hmem, hlec, hall⟩ := pickMin_spec (I := I) cs c
      have hnextc : pickMin I c cs ∈ cands I cur := by
        rcases hmem with h | h
        · rw [h, hc]; exact List.mem_cons_self
        · rw [hc]; exact List.mem_cons_of_mem _ h
      obtain ⟨hnmem, hndom, hnne⟩ := cands_mem hnextc
      have hstrict : sumRank I cur < sumRank I (pickMin I c cs) :=
        sumRank_lt_of_strict hWF hcur hnmem hndom hnne
      have hrec := ih _ hnmem (by omega)
      rcases ht : chainFrom I f (pickMin I c cs) with _ | ⟨h, t⟩
      · have h2 := chainFrom_head I f (pickMin I c cs)
        rw [ht] at h2
        simp at h2
      · rw [ht] at hrec
        rw [List.getLast?_cons_cons]
        exact hrec

/-! ## Completeness: every stable pair appears on the chain -/

theorem mrank_facts {I : Inst6} (hWF : WF6 I = true) :
    I.mrank.length = 6 ∧ ∀ r ∈ I.mrank, isRankRow6 r = true := by
  simp only [WF6, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hWF
  obtain ⟨⟨⟨hml, _⟩, hmrows⟩, _⟩ := hWF
  exact ⟨hml, fun r hr => hmrows r hr⟩

theorem partner_eq_of_rank_eq {I : Inst6} (hWF : WF6 I = true)
    {μ σ : List Nat} (hμ : μ ∈ sms6 I) (hσ : σ ∈ sms6 I) {m : Nat} (hm : m < 6)
    (h : get2 I.mrank m (μ.getD m 0) = get2 I.mrank m (σ.getD m 0)) :
    μ.getD m 0 = σ.getD m 0 := by
  obtain ⟨hlen, hrows⟩ := mrank_facts hWF
  exact rank_inj6 hlen hrows hm (perm6_getD_lt (mem_sms6_perm hμ) hm)
    (perm6_getD_lt (mem_sms6_perm hσ) hm) h

/-- Rank-walk squeeze: on a cover chain whose endpoints bracket `σ`'s
rank for man `m`, some chain element gives `m` exactly `σ`'s partner.
`no_skip` forbids any cover step from jumping over `σ`'s rank. -/
theorem chain_walk {I : Inst6} (hWF : WF6 I = true) :
    ∀ (c : List (List Nat)), List.Chain' (CoverStep I) c →
    (∀ x ∈ c, x ∈ sms6 I) →
    ∀ (σ : List Nat), σ ∈ sms6 I → ∀ (m : Nat), m < 6 →
    ∀ (first lst : List Nat), c.head? = some first → c.getLast? = some lst →
    get2 I.mrank m (first.getD m 0) ≤ get2 I.mrank m (σ.getD m 0) →
    get2 I.mrank m (σ.getD m 0) ≤ get2 I.mrank m (lst.getD m 0) →
    ∃ x ∈ c, x.getD m 0 = σ.getD m 0 := by
  intro c
  induction c with
  | nil =>
    intro _ _ σ _ m _ first lst hhead
    simp at hhead
  | cons x xs ih =>
    intro hchain hmem σ hσ m hm first lst hhead hlast hlo hhi
    have hfx : x = first := by simpa using hhead
    have hlo' : get2 I.mrank m (x.getD m 0) ≤ get2 I.mrank m (σ.getD m 0) := by
      rw [hfx]; exact hlo
    cases xs with
    | nil =>
      have hlx : x = lst := by simpa using hlast
      have hhi' : get2 I.mrank m (σ.getD m 0) ≤ get2 I.mrank m (x.getD m 0) := by
        rw [hlx]; exact hhi
      have heq : get2 I.mrank m (x.getD m 0) = get2 I.mrank m (σ.getD m 0) :=
        Nat.le_antisymm hlo' hhi'
      exact ⟨x, List.mem_cons_self,
        partner_eq_of_rank_eq hWF (hmem x List.mem_cons_self) hσ hm heq⟩
    | cons y rest =>
      obtain ⟨hxy, hchain'⟩ := List.isChain_cons_cons.1 hchain
      by_cases hcase : get2 I.mrank m (σ.getD m 0) ≤ get2 I.mrank m (x.getD m 0)
      · have heq := Nat.le_antisymm hlo' hcase
        exact ⟨x, List.mem_cons_self,
          partner_eq_of_rank_eq hWF (hmem x List.mem_cons_self) hσ hm heq⟩
      · push Not at hcase
        have hx6 : x ∈ sms6 I := hmem x List.mem_cons_self
        have hy6 : y ∈ sms6 I :=
          hmem y (List.mem_cons_of_mem _ List.mem_cons_self)
        obtain ⟨hdomxy, hnexy, hcovxy⟩ := hxy
        have hns := no_skip hWF hx6 hy6 hσ hdomxy hcovxy hm
        have hylo : get2 I.mrank m (y.getD m 0) ≤ get2 I.mrank m (σ.getD m 0) := by
          by_contra hgt
          push Not at hgt
          exact hns ⟨hcase, hgt⟩
        have hlast' : (y :: rest).getLast? = some lst := by
          rwa [List.getLast?_cons_cons] at hlast
        have hmem' : ∀ z ∈ y :: rest, z ∈ sms6 I :=
          fun z hz => hmem z (List.mem_cons_of_mem _ hz)
        obtain ⟨z, hz1, hz2⟩ :=
          ih hchain' hmem' σ hσ m hm y lst rfl hlast' hylo hhi
        exact ⟨z, List.mem_cons_of_mem _ hz1, hz2⟩

theorem stab_witness {I : Inst6} {m w : Nat} (h : stab I m w = true) :
    ∃ μ ∈ sms6 I, μ.getD m 0 = w := by
  simp only [stab, List.any_eq_true, beq_iff_eq] at h
  exact h

/-- **Chain completeness.** Every stable pair `(m, w)` of `I` is realized
by some matching on `theChain I`. -/
theorem chain_complete {I : Inst6} (hWF : WF6 I = true) {m w : Nat}
    (hm : m < 6) (hstab : stab I m w = true) :
    ∃ x ∈ theChain I, x.getD m 0 = w := by
  obtain ⟨σ, hσ, hσw⟩ := stab_witness hstab
  have hne : sms6 I ≠ [] := by
    intro h
    rw [h] at hσ
    exact absurd hσ (List.not_mem_nil)
  obtain ⟨hMmem, hMdom⟩ := manOpt_spec hWF hne
  obtain ⟨hWmem, hWdom⟩ := womanOpt_spec hWF hne
  have hfuel : sumRank I (womanOpt I) ≤ sumRank I (manOpt I) + 31 := by
    have := sumRank_le_30 hWF hWmem
    omega
  simp only [theChain]
  obtain ⟨x, hx1, hx2⟩ := chain_walk hWF (chainFrom I 31 (manOpt I))
    (chainFrom_cover hWF 31 (manOpt I) hMmem)
    (chainFrom_mem 31 (manOpt I) hMmem)
    σ hσ m hm (manOpt I) (womanOpt I)
    (chainFrom_head I 31 (manOpt I))
    (chainFrom_last hWF hne 31 (manOpt I) hMmem hfuel)
    (hMdom σ hσ m hm) (hWdom σ hσ m hm)
  exact ⟨x, hx1, hx2.trans hσw⟩
