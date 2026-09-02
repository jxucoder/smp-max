import SmpF5.Cycle6

/-!
# Chain → schedule: concatenating single-step decompositions

`chainSched I` links the single-step decompositions of consecutive
elements of `theChain I` into one schedule. Its matching sequence passes
through every chain element, so its trajectories are the chain
trajectories — the `traj`/`wtraj` data of `I` — realized by legal
cyclic steps. This is the executable form of the Validity Lemma.
-/

/-- Two permutations of `idRow6` agreeing pointwise below 6 are equal. -/
theorem perm6_ext {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) (h : ∀ x, x < 6 → μ.getD x 0 = ν.getD x 0) :
    μ = ν := by
  apply List.ext_getElem
  · rw [perm6_length hpμ, perm6_length hpν]
  · intro i h1 h2
    have hi6 : i < 6 := by rw [perm6_length hpμ] at h1; exact h1
    rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
    exact h i hi6

theorem orbAcc_all_WFStep {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) {acc : List (List Nat)} (h : OrbAcc μ ν acc) :
    ∀ st ∈ acc, WFStep st := by
  intro st hst
  obtain ⟨m0, hm06, hmov, rfl⟩ := h.1 st hst
  exact orbit_WFStep hpμ hpν hm06 hmov

theorem stepDecomp_WFStep {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) : ∀ st ∈ stepDecomp μ ν, WFStep st :=
  orbAcc_all_WFStep hpμ hpν (stepDecomp_spec hpμ hpν).1

/-- Folding `applyStep` over `stepDecomp μ ν` from `μ` lands exactly
on `ν`. -/
theorem foldl_stepDecomp_eq {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) :
    (stepDecomp μ ν).foldl (fun mu st => applyStep st mu) μ = ν := by
  have hfold : ∀ (L : List (List Nat)) (start : List Nat),
      start.Perm idRow6 → (∀ st ∈ L, WFStep st) →
      (L.foldl (fun mu st => applyStep st mu) start).Perm idRow6 := by
    intro L
    induction L with
    | nil => intro start hs _; simpa using hs
    | cons st rest ih =>
      intro start hs hWF
      rw [List.foldl_cons]
      exact ih _ (applyStep_perm (hWF st List.mem_cons_self) hs)
        (fun s hs' => hWF s (List.mem_cons_of_mem _ hs'))
  refine perm6_ext (hfold _ _ hpμ (stepDecomp_WFStep hpμ hpν)) hpν ?_
  intro x hx
  exact (stepDecomp_spec hpμ hpν).2 x hx

/-- Link the decompositions of consecutive matchings in a list. -/
noncomputable def linkSteps : List (List Nat) → List (List Nat)
  | [] => []
  | [_] => []
  | μ :: ν :: rest => stepDecomp μ ν ++ linkSteps (ν :: rest)

noncomputable def chainSched (I : Inst6) : List (List Nat) := linkSteps (theChain I)

theorem linkSteps_all_WFStep :
    ∀ (L : List (List Nat)), (∀ mu ∈ L, mu.Perm idRow6) →
    ∀ st ∈ linkSteps L, WFStep st := by
  intro L
  induction L with
  | nil => intro _ st hst; simp [linkSteps] at hst
  | cons μ rest ih =>
    cases rest with
    | nil => intro _ st hst; simp [linkSteps] at hst
    | cons ν rest2 =>
      intro hperm st hst
      have hpμ : μ.Perm idRow6 := hperm μ List.mem_cons_self
      have hpν : ν.Perm idRow6 :=
        hperm ν (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [linkSteps, List.mem_append] at hst
      rcases hst with h | h
      · exact stepDecomp_WFStep hpμ hpν st h
      · exact ih (fun mu hmu => hperm mu (List.mem_cons_of_mem _ hmu)) st h

/-! ## The schedule threads through the chain -/

/-- Folding `applyStep` over `linkSteps (ν :: rest)` from `ν` lands on
the last element. -/
theorem linkSteps_foldl_last :
    ∀ (rest : List (List Nat)) (ν : List Nat),
    ν.Perm idRow6 → (∀ mu ∈ rest, mu.Perm idRow6) →
    (linkSteps (ν :: rest)).foldl (fun mu st => applyStep st mu) ν
      = (ν :: rest).getLast (by simp) := by
  intro rest
  induction rest with
  | nil =>
    intro ν _ _
    simp [linkSteps]
  | cons w rest2 ih =>
    intro ν hpν hrest
    have hpw : w.Perm idRow6 := hrest w List.mem_cons_self
    have hrest2 : ∀ mu ∈ rest2, mu.Perm idRow6 :=
      fun mu hmu => hrest mu (List.mem_cons_of_mem _ hmu)
    simp only [linkSteps]
    rw [List.foldl_append, foldl_stepDecomp_eq hpν hpw]
    rw [ih w hpw hrest2]
    rw [List.getLast_cons_cons]

/-- Generalized `scanl` over an append. -/
theorem scanl_append_f {a : List Nat} (L₁ L₂ : List (List Nat)) :
    List.scanl (fun mu st => applyStep st mu) a (L₁ ++ L₂)
      = List.scanl (fun mu st => applyStep st mu) a L₁ ++
        (List.scanl (fun mu st => applyStep st mu)
          (L₁.foldl (fun mu st => applyStep st mu) a) L₂).tail := by
  induction L₁ generalizing a with
  | nil =>
    cases L₂ with
    | nil => simp
    | cons st rest => simp [List.scanl_cons]
  | cons st rest ih => simp [List.scanl_cons, ih]

/-! ## Stutter-invariance of destutter (abstract) -/

section Destutter
variable {α : Type} [DecidableEq α]

/-- Removing one adjacent duplicate preserves `destutter (≠)`. -/
theorem destutter_ne_dup (a : α) (l : List α) :
    (a :: a :: l).destutter (· ≠ ·) = (a :: l).destutter (· ≠ ·) := by
  rw [List.destutter_cons_cons]
  simp only [ne_eq, not_true_eq_false, if_false]
  rw [List.destutter_cons']

/-- A run of `a`'s collapses under `destutter (≠)`. -/
theorem destutter_ne_replicate (a : α) (n : Nat) (l : List α) :
    ((List.replicate (n + 1) a) ++ l).destutter (· ≠ ·)
      = (a :: l).destutter (· ≠ ·) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    rw [show List.replicate (k + 1) a ++ l = a :: (List.replicate k a ++ l) by
      rw [List.replicate_succ, List.cons_append]]
    rw [destutter_ne_dup]
    rw [← List.cons_append, ← List.replicate_succ]
    exact ih

/-- Prepending a run of `a` before a list already headed by `a`
collapses. -/
theorem destutter_ne_run_cons (a : α) (n : Nat) (l : List α) :
    ((List.replicate n a) ++ a :: l).destutter (· ≠ ·)
      = (a :: l).destutter (· ≠ ·) := by
  have : (List.replicate n a) ++ a :: l
      = (List.replicate (n + 1) a) ++ l := by
    rw [List.replicate_succ']
    simp
  rw [this, destutter_ne_replicate]

end Destutter

/-! ## Block column is two-valued -/

/-- Scanl version of `foldl_orbits`: over a disjoint-orbit list, every
visited matching sends each man to his `μ'`-partner or his `ν`-partner. -/
theorem scanl_orbits_two_valued {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) :
    ∀ (L : List (List Nat)) (μ' : List Nat), OrbAcc μ ν L →
    (∀ y ∈ L.flatten, μ'.getD y 0 = μ.getD y 0) →
    ∀ σ ∈ List.scanl (fun mu st => applyStep st mu) μ' L,
    ∀ x, x < 6 → σ.getD x 0 = μ'.getD x 0 ∨ σ.getD x 0 = ν.getD x 0 := by
  intro L
  induction L with
  | nil =>
    intro μ' _ _ σ hσ x hx
    simp only [List.scanl_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hσ
    left; rw [hσ]
  | cons O rest ih =>
    intro μ' hOrb hagree σ hσ x hx
    obtain ⟨horbs, hdisj⟩ := hOrb
    obtain ⟨m0, hm06, hmov, hOdef⟩ := horbs O List.mem_cons_self
    have hOrbRest : OrbAcc μ ν rest :=
      ⟨fun st hst => horbs st (List.mem_cons_of_mem _ hst), hdisj.of_cons⟩
    have hdisjO : ∀ z ∈ O, ∀ t ∈ rest, z ∉ t :=
      fun z hz t ht => (List.pairwise_cons.1 hdisj).1 t ht z hz
    rw [List.scanl_cons] at hσ
    rcases List.mem_cons.1 hσ with rfl | hσ'
    · left; rfl
    · -- base for the tail: applyStep O μ'
      have hagreeO : ∀ y ∈ orbit μ ν m0, μ'.getD y 0 = μ.getD y 0 := by
        intro y hy
        exact hagree y (List.mem_flatten.2 ⟨O, List.mem_cons_self,
          hOdef ▸ hy⟩)
      -- applyStep O μ' is two-valued vs μ'
      have hbase2 : ∀ z, z < 6 →
          (applyStep O μ').getD z 0 = μ'.getD z 0 ∨
          (applyStep O μ').getD z 0 = ν.getD z 0 := by
        intro z hz
        by_cases hzO : z ∈ O
        · right
          subst hOdef
          exact applyStep_orbit_moved' hpμ hpν hm06 hagreeO hzO hz
        · left; exact applyStep_getD_notMem hz hzO
      have hagree' : ∀ y ∈ rest.flatten,
          (applyStep O μ').getD y 0 = μ.getD y 0 := by
        intro y hy
        have hy6 : y < 6 := orbAcc_flatten_lt6 hpμ hpν hOrbRest hy
        have hynO : y ∉ O := by
          intro hyO
          obtain ⟨t, ht, hyt⟩ := List.mem_flatten.1 hy
          exact hdisjO y hyO t ht hyt
        rw [applyStep_getD_notMem hy6 hynO]
        obtain ⟨t, ht, hyt⟩ := List.mem_flatten.1 hy
        exact hagree y (List.mem_flatten.2 ⟨t,
          List.mem_cons_of_mem _ ht, hyt⟩)
      have hIH := ih (applyStep O μ') hOrbRest hagree' σ hσ' x hx
      rcases hIH with h | h
      · rw [h]; exact hbase2 x hx
      · right; exact h

/-! ## Block column destutters to two values -/

section Destutter2
variable {α : Type} [DecidableEq α]

theorem destutter_ne_replicate_eq (a : α) (n : Nat) :
    (List.replicate (n + 1) a).destutter (· ≠ ·) = [a] := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ]
    rw [show a :: List.replicate (k + 1) a = a :: a :: List.replicate k a by
      rw [List.replicate_succ]]
    rw [destutter_ne_dup, ← List.replicate_succ, ih]

theorem destutter_ne_cons_replicate {a b : α} (n : Nat) (hab : a ≠ b) :
    (a :: List.replicate (n + 1) b).destutter (· ≠ ·) = [a, b] := by
  rw [List.replicate_succ, List.destutter_cons_cons, if_pos hab,
    ← List.destutter_cons', ← List.replicate_succ, destutter_ne_replicate_eq]

end Destutter2

section DestutterMid
variable {α : Type} [DecidableEq α]

/-- Removing one duplicated element in the middle preserves
`destutter'`. -/
theorem destutter'_ne_dup_mid :
    ∀ (l : List α) (b x : α) (t : List α),
    (l ++ x :: x :: t).destutter' (· ≠ ·) b
      = (l ++ x :: t).destutter' (· ≠ ·) b := by
  intro l
  induction l with
  | nil =>
    intro b x t
    simp only [List.nil_append]
    have hxx : ¬ ((x : α) ≠ x) := by simp
    by_cases hbx : b ≠ x
    · rw [List.destutter'_cons_pos _ hbx, List.destutter'_cons_pos _ hbx,
        List.destutter'_cons_neg _ hxx]
    · rw [List.destutter'_cons_neg _ hbx, List.destutter'_cons_neg _ hbx]
  | cons a l' ih =>
    intro b x t
    simp only [List.cons_append]
    by_cases hba : b ≠ a
    · rw [List.destutter'_cons_pos _ hba, List.destutter'_cons_pos _ hba,
        ih a x t]
    · rw [List.destutter'_cons_neg _ hba, List.destutter'_cons_neg _ hba,
        ih b x t]

/-- Junction duplicate removal: a list ending in `x` followed by
`x :: t` collapses the duplicate. -/
theorem destutter_ne_join_concat (l' : List α) (x : α) (t : List α) :
    ((l' ++ [x]) ++ x :: t).destutter (· ≠ ·)
      = ((l' ++ [x]) ++ t).destutter (· ≠ ·) := by
  cases l' with
  | nil =>
    simp only [List.nil_append, List.singleton_append]
    exact destutter_ne_dup x t
  | cons a l'' =>
    have e1 : (a :: l'') ++ [x] ++ x :: t
        = (a :: l'') ++ x :: x :: t := by simp
    have e2 : (a :: l'') ++ [x] ++ t = (a :: l'') ++ x :: t := by simp
    rw [e1, e2, List.cons_append, List.cons_append,
      List.destutter_cons', List.destutter_cons']
    exact destutter'_ne_dup_mid l'' a x t

theorem destutter_ne_join {l : List α} {x : α} (t : List α)
    (hl : l.getLast? = some x) :
    (l ++ x :: t).destutter (· ≠ ·) = (l ++ t).destutter (· ≠ ·) := by
  induction l using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton l' a _ =>
    rw [List.getLast?_concat] at hl
    have hax : a = x := Option.some_inj.1 hl
    subst hax
    exact destutter_ne_join_concat l' a t

end DestutterMid

section DestutterSplit
variable {α : Type} [DecidableEq α]

theorem list_eq_head_tail {l : List α} {a : α} (h : l.head? = some a) :
    l = a :: l.tail := by
  cases l with
  | nil => simp at h
  | cons c t =>
    rw [List.head?_cons, Option.some_inj] at h
    subst h; rfl

theorem destutter'_head_cons (b : α) (B : List α) :
    B.destutter' (· ≠ ·) b = b :: (B.destutter' (· ≠ ·) b).tail :=
  list_eq_head_tail (destutter'_head? B b)

theorem destutter_ne_cons_head (a : α) (B : List α) :
    (a :: B).destutter (· ≠ ·) = a :: ((a :: B).destutter (· ≠ ·)).tail := by
  apply list_eq_head_tail
  rw [List.destutter_cons']
  exact destutter'_head? B a

theorem destutter'_ne_snoc_append :
    ∀ (A' : List α) (s b : α) (B : List α),
    ((A' ++ [b]) ++ B).destutter' (· ≠ ·) s
      = (A' ++ [b]).destutter' (· ≠ ·) s
        ++ ((b :: B).destutter (· ≠ ·)).tail := by
  intro A'
  induction A' with
  | nil =>
    intro s b B
    simp only [List.nil_append, List.singleton_append]
    have hRtail : ((b :: B).destutter (· ≠ ·)).tail
        = (B.destutter' (· ≠ ·) b).tail := by rw [List.destutter_cons']
    by_cases hsb : s ≠ b
    · have hL : (b :: B).destutter' (· ≠ ·) s = s :: B.destutter' (· ≠ ·) b :=
        List.destutter'_cons_pos B hsb
      have hR1 : (b :: ([] : List α)).destutter' (· ≠ ·) s = [s, b] := by
        rw [List.destutter'_cons_pos [] hsb, List.destutter'_nil]
      rw [hL, hR1, hRtail]
      conv_lhs => rw [destutter'_head_cons b B]
      rfl
    · have hbe : s = b := by simpa using hsb
      subst hbe
      have hL : (s :: B).destutter' (· ≠ ·) s = B.destutter' (· ≠ ·) s :=
        List.destutter'_cons_neg B (by simp)
      have hR1 : (s :: ([] : List α)).destutter' (· ≠ ·) s = [s] := by
        rw [List.destutter'_cons_neg [] (by simp), List.destutter'_nil]
      rw [hL, hR1, hRtail]
      conv_lhs => rw [destutter'_head_cons s B]
      rfl
  | cons a A'' ih =>
    intro s b B
    simp only [List.cons_append]
    by_cases hsa : s ≠ a
    · rw [List.destutter'_cons_pos _ hsa, List.destutter'_cons_pos _ hsa,
        ih a b B, List.cons_append]
    · rw [List.destutter'_cons_neg _ hsa, List.destutter'_cons_neg _ hsa,
        ih s b B]

theorem destutter_ne_append_getLast {A : List α} {b : α} (B : List α)
    (hA : A.getLast? = some b) :
    (A ++ B).destutter (· ≠ ·)
      = A.destutter (· ≠ ·) ++ ((b :: B).destutter (· ≠ ·)).tail := by
  induction A using List.reverseRecOn with
  | nil => simp at hA
  | append_singleton A' a _ =>
    rw [List.getLast?_concat] at hA
    obtain rfl : a = b := Option.some_inj.1 hA
    cases A' with
    | nil =>
      simp only [List.nil_append, List.singleton_append,
        List.destutter_singleton]
      conv_lhs => rw [destutter_ne_cons_head a B]
    | cons c A'' =>
      have hL : ((c :: A'') ++ [a]) ++ B = c :: ((A'' ++ [a]) ++ B) := by
        simp
      have hR : (c :: A'') ++ [a] = c :: (A'' ++ [a]) := by simp
      rw [hL, hR, List.destutter_cons', List.destutter_cons']
      exact destutter'_ne_snoc_append A'' c a B

end DestutterSplit



/-- Off the orbit union, the whole scanl column is constant. -/
theorem scanl_notMem_const :
    ∀ (L : List (List Nat)) (μ' : List Nat) (m : Nat), m < 6 →
    m ∉ L.flatten →
    ∀ σ ∈ List.scanl (fun mu st => applyStep st mu) μ' L,
    σ.getD m 0 = μ'.getD m 0 := by
  intro L
  induction L with
  | nil =>
    intro μ' m hm hnm σ hσ
    simp only [List.scanl_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hσ
    rw [hσ]
  | cons O rest ih =>
    intro μ' m hm hnm σ hσ
    rw [List.flatten_cons, List.mem_append, not_or] at hnm
    obtain ⟨hnO, hnrest⟩ := hnm
    rw [List.scanl_cons] at hσ
    rcases List.mem_cons.1 hσ with rfl | hσ'
    · rfl
    · have := ih (applyStep O μ') m hm hnrest σ hσ'
      rw [this, applyStep_getD_notMem hm hnO]

theorem scanl_eq_cons (f : List Nat → List Nat → List Nat) (a : List Nat)
    (L : List (List Nat)) : ∃ T, List.scanl f a L = a :: T := by
  cases L with
  | nil => exact ⟨[], rfl⟩
  | cons s rest => exact ⟨_, by rw [List.scanl_cons]⟩

/-- The destuttered partner column over a disjoint-orbit list: two
values (`μ'(m)` then `ν(m)`) if `m` moves in the block, one otherwise. -/
theorem block_col_destutter {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) {m : Nat} (hm : m < 6) :
    ∀ (L : List (List Nat)) (μ' : List Nat), OrbAcc μ ν L →
    (∀ y ∈ L.flatten, μ'.getD y 0 = μ.getD y 0) →
    (((List.scanl (fun mu st => applyStep st mu) μ' L).map
      (fun σ => σ.getD m 0)).destutter (· ≠ ·)) =
      if m ∈ L.flatten then [μ'.getD m 0, ν.getD m 0]
      else [μ'.getD m 0] := by
  intro L
  induction L with
  | nil =>
    intro μ' _ _
    simp [List.scanl_nil]
  | cons O rest ih =>
    intro μ' hOrb hagree
    obtain ⟨horbs, hdisj⟩ := hOrb
    obtain ⟨m0, hm06, hmov, hOdef⟩ := horbs O List.mem_cons_self
    have hOrbRest : OrbAcc μ ν rest :=
      ⟨fun st hst => horbs st (List.mem_cons_of_mem _ hst), hdisj.of_cons⟩
    have hdisjO : ∀ z ∈ O, ∀ t ∈ rest, z ∉ t :=
      fun z hz t ht => (List.pairwise_cons.1 hdisj).1 t ht z hz
    have hagreeO : ∀ y ∈ orbit μ ν m0, μ'.getD y 0 = μ.getD y 0 := by
      intro y hy
      exact hagree y (List.mem_flatten.2 ⟨O, List.mem_cons_self,
        hOdef ▸ hy⟩)
    have hagree' : ∀ y ∈ rest.flatten,
        (applyStep O μ').getD y 0 = μ.getD y 0 := by
      intro y hy
      have hy6 : y < 6 := orbAcc_flatten_lt6 hpμ hpν hOrbRest hy
      have hynO : y ∉ O := by
        intro hyO
        obtain ⟨t, ht, hyt⟩ := List.mem_flatten.1 hy
        exact hdisjO y hyO t ht hyt
      rw [applyStep_getD_notMem hy6 hynO]
      obtain ⟨t, ht, hyt⟩ := List.mem_flatten.1 hy
      exact hagree y (List.mem_flatten.2 ⟨t,
        List.mem_cons_of_mem _ ht, hyt⟩)
    rw [List.scanl_cons, List.map_cons]
    by_cases hmO : m ∈ O
    · -- m moves in this orbit: partner jumps to ν(m) and stays
      have hbaseν : (applyStep O μ').getD m 0 = ν.getD m 0 := by
        subst hOdef
        exact applyStep_orbit_moved' hpμ hpν hm06 hagreeO hmO hm
      have hmnrest : m ∉ rest.flatten := by
        intro hc
        obtain ⟨t, ht, hmt⟩ := List.mem_flatten.1 hc
        exact hdisjO m hmO t ht hmt
      have hconst : ∀ σ ∈ List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest, σ.getD m 0 = ν.getD m 0 := fun σ hσ =>
        (scanl_notMem_const rest (applyStep O μ') m hm hmnrest σ hσ).trans
          hbaseν
      have htaileq : (List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).map (fun σ => σ.getD m 0)
          = List.replicate ((List.scanl (fun mu st => applyStep st mu)
              (applyStep O μ') rest).length) (ν.getD m 0) := by
        rw [List.eq_replicate_iff]
        refine ⟨by rw [List.length_map], ?_⟩
        intro b hb
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hb
        exact hconst σ hσ
      have hlenpos : 0 < (List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).length := by
        obtain ⟨T, hT⟩ := scanl_eq_cons (fun mu st => applyStep st mu)
          (applyStep O μ') rest
        rw [hT]; simp
      obtain ⟨k, hk⟩ : ∃ k, (List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).length = k + 1 :=
        ⟨(List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).length - 1, by omega⟩
      have hmovm : moved μ ν m :=
        orbit_all_moved hpμ hpν hm06 hmov m (hOdef ▸ hmO)
      have hμm : μ'.getD m 0 = μ.getD m 0 := hagree m
        (List.mem_flatten.2 ⟨O, List.mem_cons_self, hmO⟩)
      have hne : μ'.getD m 0 ≠ ν.getD m 0 := by rw [hμm]; exact hmovm
      rw [htaileq, hk, destutter_ne_cons_replicate k hne,
        if_pos (List.mem_flatten.2 ⟨O, List.mem_cons_self, hmO⟩)]
    · -- m fixed by this orbit: leading duplicate collapses
      have hbasefix : (applyStep O μ').getD m 0 = μ'.getD m 0 :=
        applyStep_getD_notMem hm hmO
      obtain ⟨T, hT⟩ := scanl_eq_cons (fun mu st => applyStep st mu)
        (applyStep O μ') rest
      have hcolM : (List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).map (fun σ => σ.getD m 0)
          = μ'.getD m 0 :: T.map (fun σ => σ.getD m 0) := by
        rw [hT, List.map_cons, hbasefix]
      rw [hcolM, destutter_ne_dup, ← hcolM,
        ih (applyStep O μ') hOrbRest hagree', hbasefix]
      by_cases hmr : m ∈ rest.flatten
      · rw [if_pos hmr, if_pos (List.mem_flatten.2 (by
          obtain ⟨t, ht, hmt⟩ := List.mem_flatten.1 hmr
          exact ⟨t, List.mem_cons_of_mem _ ht, hmt⟩))]
      · rw [if_neg hmr, if_neg (by
          rw [List.flatten_cons, List.mem_append]
          exact fun h => hmr (h.resolve_left hmO))]

/-! ## Assembly helpers -/

theorem foldl_notMem_const :
    ∀ (L : List (List Nat)) (μ' : List Nat) (m : Nat), m < 6 →
    m ∉ L.flatten →
    (L.foldl (fun mu st => applyStep st mu) μ').getD m 0 = μ'.getD m 0 := by
  intro L
  induction L with
  | nil => intro μ' m _ _; rfl
  | cons O rest ih =>
    intro μ' m hm6 hnm
    rw [List.flatten_cons, List.mem_append, not_or] at hnm
    obtain ⟨hnO, hnrest⟩ := hnm
    rw [List.foldl_cons, ih (applyStep O μ') m hm6 hnrest]
    exact applyStep_getD_notMem hm6 hnO

theorem scanl_getLast?_foldl (f : List Nat → List Nat → List Nat)
    (a : List Nat) (L : List (List Nat)) :
    (List.scanl f a L).getLast? = some (L.foldl f a) := by
  induction L generalizing a with
  | nil => rfl
  | cons s rest ih =>
    rw [List.scanl_cons, List.getLast?_cons_of_ne_nil (by
      simp [List.scanl_ne_nil]), ih, List.foldl_cons]

theorem stepDecomp_flatten_iff_moved {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) {m : Nat} (hm : m < 6) :
    m ∈ (stepDecomp μ ν).flatten ↔ μ.getD m 0 ≠ ν.getD m 0 := by
  constructor
  · intro hmem
    obtain ⟨hOrb, _⟩ := stepDecomp_spec hpμ hpν
    obtain ⟨st, hst, hmst⟩ := List.mem_flatten.1 hmem
    obtain ⟨m0, hm06, hmov, rfl⟩ := hOrb.1 st hst
    exact orbit_all_moved hpμ hpν hm06 hmov m hmst
  · intro hmov
    by_contra hnm
    have h1 := foldl_notMem_const (stepDecomp μ ν) μ m hm hnm
    have h2 := (stepDecomp_spec hpμ hpν).2 m hm
    rw [h1] at h2
    exact hmov h2

/-! ## strajM = traj -/

/-- Master lemma: the destuttered partner column of the schedule
generated from `μ0 :: rest` equals that of the matching list itself. -/
theorem col_destutter_link {m : Nat} (hm : m < 6) :
    ∀ (rest : List (List Nat)) (μ0 : List Nat), μ0.Perm idRow6 →
    (∀ mu ∈ rest, mu.Perm idRow6) →
    ((List.scanl (fun mu st => applyStep st mu) μ0
        (linkSteps (μ0 :: rest))).map (fun σ => σ.getD m 0)).destutter (· ≠ ·)
      = ((μ0 :: rest).map (fun σ => σ.getD m 0)).destutter (· ≠ ·) := by
  intro rest
  induction rest with
  | nil =>
    intro μ0 _ _
    simp [linkSteps, List.scanl_nil]
  | cons μ1 rest2 ih =>
    intro μ0 hp0 hprest
    have hp1 : μ1.Perm idRow6 := hprest μ1 List.mem_cons_self
    have hprest2 : ∀ mu ∈ rest2, mu.Perm idRow6 :=
      fun mu hmu => hprest mu (List.mem_cons_of_mem _ hmu)
    -- split the scanl
    have hlink : linkSteps (μ0 :: μ1 :: rest2)
        = stepDecomp μ0 μ1 ++ linkSteps (μ1 :: rest2) := rfl
    rw [hlink, scanl_append_f, foldl_stepDecomp_eq hp0 hp1, List.map_append,
      List.map_tail]
    -- names
    set Afull := List.scanl (fun mu st => applyStep st mu) μ0
      (stepDecomp μ0 μ1) with hAf
    set Bfull := List.scanl (fun mu st => applyStep st mu) μ1
      (linkSteps (μ1 :: rest2)) with hBf
    set A := Afull.map (fun σ => σ.getD m 0) with hA
    set Bcol := Bfull.map (fun σ => σ.getD m 0) with hBc
    -- A ends in μ1(m)
    have hAlast : A.getLast? = some (μ1.getD m 0) := by
      rw [hA, getLast?_map', hAf, scanl_getLast?_foldl,
        foldl_stepDecomp_eq hp0 hp1]
      rfl
    -- Bcol starts with μ1(m)
    have hBhead : Bcol = μ1.getD m 0 :: Bcol.tail := by
      apply list_eq_head_tail
      rw [hBc, List.head?_map, hBf]
      obtain ⟨T, hT⟩ := scanl_eq_cons (fun mu st => applyStep st mu) μ1
        (linkSteps (μ1 :: rest2))
      rw [hT]; rfl
    -- junction: destutter (A ++ Bcol.tail) = destutter (A ++ Bcol)
    have hjoin : (A ++ Bcol.tail).destutter (· ≠ ·)
        = (A ++ Bcol).destutter (· ≠ ·) := by
      conv_rhs => rw [hBhead]
      exact (destutter_ne_join Bcol.tail hAlast).symm
    -- append split
    have hsplit : (A ++ Bcol).destutter (· ≠ ·)
        = A.destutter (· ≠ ·)
          ++ ((μ1.getD m 0 :: Bcol).destutter (· ≠ ·)).tail :=
      destutter_ne_append_getLast Bcol hAlast
    -- (μ1(m) :: Bcol) destutter tail = (destutter Bcol).tail
    have hBcoldup : ((μ1.getD m 0 :: Bcol).destutter (· ≠ ·)).tail
        = (Bcol.destutter (· ≠ ·)).tail := by
      conv_lhs => rw [hBhead]
      rw [destutter_ne_dup]
      conv_rhs => rw [hBhead]
    -- IH on Bcol
    have hIH : Bcol.destutter (· ≠ ·)
        = ((μ1 :: rest2).map (fun σ => σ.getD m 0)).destutter (· ≠ ·) := by
      rw [hBc, hBf]
      exact ih μ1 hp1 hprest2
    -- block col destutter
    have hblock : A.destutter (· ≠ ·)
        = if m ∈ (stepDecomp μ0 μ1).flatten
          then [μ0.getD m 0, μ1.getD m 0] else [μ0.getD m 0] := by
      rw [hA, hAf]
      exact block_col_destutter hp0 hp1 hm (stepDecomp μ0 μ1) μ0
        (stepDecomp_spec hp0 hp1).1 (fun y _ => rfl)
    rw [hjoin, hsplit, hblock, hBcoldup, hIH]
    -- RHS target
    have hRHS : ((μ0 :: μ1 :: rest2).map (fun σ => σ.getD m 0)).destutter
        (· ≠ ·)
        = (μ0.getD m 0 :: μ1.getD m 0 :: rest2.map (fun σ => σ.getD m 0)
          ).destutter (· ≠ ·) := by simp [List.map_cons]
    rw [hRHS]
    -- RHS_B
    set RB := ((μ1 :: rest2).map (fun σ => σ.getD m 0)).destutter (· ≠ ·)
      with hRB
    have hRBhead : RB = μ1.getD m 0 :: RB.tail := by
      rw [hRB, List.map_cons]
      apply list_eq_head_tail
      rw [List.destutter_cons']
      exact destutter'_head? _ _
    by_cases hmem : m ∈ (stepDecomp μ0 μ1).flatten
    · rw [if_pos hmem]
      have hne : μ0.getD m 0 ≠ μ1.getD m 0 :=
        (stepDecomp_flatten_iff_moved hp0 hp1 hm).1 hmem
      simp only [List.cons_append, List.nil_append]
      rw [← hRBhead, List.destutter_cons_cons, if_pos hne,
        ← List.destutter_cons', hRB, List.map_cons]
    · rw [if_neg hmem]
      have heq : μ0.getD m 0 = μ1.getD m 0 := by
        by_contra hc
        exact hmem ((stepDecomp_flatten_iff_moved hp0 hp1 hm).2 hc)
      simp only [List.cons_append, List.nil_append]
      rw [heq, ← hRBhead, destutter_ne_dup, hRB, List.map_cons]

/-- **The schedule realizes the chain trajectories** (man side), under
the normalization `manOpt I = idRow6` so the schedule starts at the
identity. -/
theorem strajM_eq_traj {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ [])
    (hmo : manOpt I = idRow6) {m : Nat} (hm : m < 6) :
    strajM (chainSched I) m = traj I m := by
  obtain ⟨hMmem, _⟩ := manOpt_spec hWF hne
  have hhead : (theChain I).head? = some (manOpt I) :=
    chainFrom_head I 31 (manOpt I)
  have hchain : theChain I = idRow6 :: (theChain I).tail := by
    have h := list_eq_head_tail hhead
    rwa [hmo] at h
  have hpid : idRow6.Perm idRow6 := List.Perm.refl _
  have hptail : ∀ mu ∈ (theChain I).tail, mu.Perm idRow6 := by
    intro mu hmu
    exact chain_mem_perm hWF hne (List.mem_of_mem_tail hmu)
  have hkey := col_destutter_link hm (theChain I).tail idRow6 hpid hptail
  unfold strajM chainSched schedMatchings traj
  conv_lhs => rw [hchain]
  rw [hkey, ← hchain]

/-! ## Generic column assembly

The junction/append-split machinery is agnostic to *which* coordinate
of the matching we track. Abstract it over a column function `κ`, with
the per-block destutter as a hypothesis; instantiate for the man column
(`σ.getD m 0`) and the woman column (`idxOf w σ`). -/

theorem col_destutter_link_gen (κ : List Nat → Nat)
    (hblock : ∀ (μ ν : List Nat), μ.Perm idRow6 → ν.Perm idRow6 →
      ((List.scanl (fun mu st => applyStep st mu) μ
        (stepDecomp μ ν)).map κ).destutter (· ≠ ·)
        = if κ μ ≠ κ ν then [κ μ, κ ν] else [κ μ]) :
    ∀ (rest : List (List Nat)) (μ0 : List Nat), μ0.Perm idRow6 →
    (∀ mu ∈ rest, mu.Perm idRow6) →
    ((List.scanl (fun mu st => applyStep st mu) μ0
        (linkSteps (μ0 :: rest))).map κ).destutter (· ≠ ·)
      = ((μ0 :: rest).map κ).destutter (· ≠ ·) := by
  intro rest
  induction rest with
  | nil =>
    intro μ0 _ _
    simp [linkSteps, List.scanl_nil]
  | cons μ1 rest2 ih =>
    intro μ0 hp0 hprest
    have hp1 : μ1.Perm idRow6 := hprest μ1 List.mem_cons_self
    have hprest2 : ∀ mu ∈ rest2, mu.Perm idRow6 :=
      fun mu hmu => hprest mu (List.mem_cons_of_mem _ hmu)
    have hlink : linkSteps (μ0 :: μ1 :: rest2)
        = stepDecomp μ0 μ1 ++ linkSteps (μ1 :: rest2) := rfl
    rw [hlink, scanl_append_f, foldl_stepDecomp_eq hp0 hp1, List.map_append,
      List.map_tail]
    set Afull := List.scanl (fun mu st => applyStep st mu) μ0
      (stepDecomp μ0 μ1) with hAf
    set Bfull := List.scanl (fun mu st => applyStep st mu) μ1
      (linkSteps (μ1 :: rest2)) with hBf
    set A := Afull.map κ with hA
    set Bcol := Bfull.map κ with hBc
    have hAlast : A.getLast? = some (κ μ1) := by
      rw [hA, getLast?_map', hAf, scanl_getLast?_foldl,
        foldl_stepDecomp_eq hp0 hp1]
      rfl
    have hBhead : Bcol = κ μ1 :: Bcol.tail := by
      apply list_eq_head_tail
      rw [hBc, List.head?_map, hBf]
      obtain ⟨T, hT⟩ := scanl_eq_cons (fun mu st => applyStep st mu) μ1
        (linkSteps (μ1 :: rest2))
      rw [hT]; rfl
    have hjoin : (A ++ Bcol.tail).destutter (· ≠ ·)
        = (A ++ Bcol).destutter (· ≠ ·) := by
      conv_rhs => rw [hBhead]
      exact (destutter_ne_join Bcol.tail hAlast).symm
    have hsplit : (A ++ Bcol).destutter (· ≠ ·)
        = A.destutter (· ≠ ·) ++ ((κ μ1 :: Bcol).destutter (· ≠ ·)).tail :=
      destutter_ne_append_getLast Bcol hAlast
    have hBcoldup : ((κ μ1 :: Bcol).destutter (· ≠ ·)).tail
        = (Bcol.destutter (· ≠ ·)).tail := by
      conv_lhs => rw [hBhead]
      rw [destutter_ne_dup]
      conv_rhs => rw [hBhead]
    have hIH : Bcol.destutter (· ≠ ·)
        = ((μ1 :: rest2).map κ).destutter (· ≠ ·) := by
      rw [hBc, hBf]; exact ih μ1 hp1 hprest2
    have hblk : A.destutter (· ≠ ·)
        = if κ μ0 ≠ κ μ1 then [κ μ0, κ μ1] else [κ μ0] := by
      rw [hA, hAf]; exact hblock μ0 μ1 hp0 hp1
    rw [hjoin, hsplit, hblk, hBcoldup, hIH]
    have hRHS : ((μ0 :: μ1 :: rest2).map κ).destutter (· ≠ ·)
        = (κ μ0 :: κ μ1 :: rest2.map κ).destutter (· ≠ ·) := by
      simp [List.map_cons]
    rw [hRHS]
    set RB := ((μ1 :: rest2).map κ).destutter (· ≠ ·) with hRB
    have hRBhead : RB = κ μ1 :: RB.tail := by
      rw [hRB, List.map_cons]
      apply list_eq_head_tail
      rw [List.destutter_cons']
      exact destutter'_head? _ _
    by_cases hne : κ μ0 ≠ κ μ1
    · rw [if_pos hne]
      simp only [List.cons_append, List.nil_append]
      rw [← hRBhead, List.destutter_cons_cons, if_pos hne,
        ← List.destutter_cons', hRB, List.map_cons]
    · rw [if_neg hne]
      have heq : κ μ0 = κ μ1 := by simpa using hne
      simp only [List.cons_append, List.nil_append]
      rw [heq, ← hRBhead, destutter_ne_dup, hRB, List.map_cons]

/-- Man-column block destutter in `κ`-form. -/
theorem block_man_kappa {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) {m : Nat} (hm : m < 6) :
    ((List.scanl (fun mu st => applyStep st mu) μ
      (stepDecomp μ ν)).map (fun σ => σ.getD m 0)).destutter (· ≠ ·)
      = if μ.getD m 0 ≠ ν.getD m 0
        then [μ.getD m 0, ν.getD m 0] else [μ.getD m 0] := by
  rw [block_col_destutter hpμ hpν hm (stepDecomp μ ν) μ
    (stepDecomp_spec hpμ hpν).1 (fun y _ => rfl)]
  by_cases hmem : m ∈ (stepDecomp μ ν).flatten
  · rw [if_pos hmem, if_pos ((stepDecomp_flatten_iff_moved hpμ hpν hm).1 hmem)]
  · rw [if_neg hmem, if_neg (fun hc =>
      hmem ((stepDecomp_flatten_iff_moved hpμ hpν hm).2 hc))]

/-! ## Woman column: how the husband of `w` changes under a step -/

theorem applyStep_idxOf_notMem_husband {O μ' : List Nat} (hO : WFStep O)
    (hμ' : μ'.Perm idRow6) {w : Nat} (hw : w < 6) (hnh : idxOf w μ' ∉ O) :
    idxOf w (applyStep O μ') = idxOf w μ' := by
  have ha6 : idxOf w μ' < 6 := idxOf_lt6 hμ' hw
  have hval : (applyStep O μ').getD (idxOf w μ') 0 = w := by
    rw [applyStep_getD_notMem ha6 hnh]
    exact getD_idxOf (perm6_mem hμ' hw)
  exact partner_idxOf_of_eq (applyStep_perm hO hμ') ha6 hval

theorem applyStep_idxOf_mem_husband {O μ' : List Nat} (hO : WFStep O)
    (hμ' : μ'.Perm idRow6) {w : Nat} (hw : w < 6) (hh : idxOf w μ' ∈ O) :
    idxOf w (applyStep O μ') ∈ O := by
  by_contra hnew
  have hp := applyStep_perm hO hμ'
  have hnew6 : idxOf w (applyStep O μ') < 6 := idxOf_lt6 hp hw
  have hval : (applyStep O μ').getD (idxOf w (applyStep O μ')) 0 = w :=
    getD_idxOf (perm6_mem hp hw)
  rw [applyStep_getD_notMem hnew6 hnew] at hval
  have heqi : idxOf w μ' = idxOf w (applyStep O μ') :=
    partner_idxOf_of_eq hμ' hnew6 hval
  exact hnew (heqi ▸ hh)

theorem scanl_idxOf_notMem_husband :
    ∀ (L : List (List Nat)) (μ' : List Nat), (∀ st ∈ L, WFStep st) →
    μ'.Perm idRow6 → {w : Nat} → w < 6 → idxOf w μ' ∉ L.flatten →
    ∀ σ ∈ List.scanl (fun mu st => applyStep st mu) μ' L,
    idxOf w σ = idxOf w μ' := by
  intro L
  induction L with
  | nil =>
    intro μ' _ _ w _ _ σ hσ
    simp only [List.scanl_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hσ
    rw [hσ]
  | cons O rest ih =>
    intro μ' hWF hμ' w hw hnh σ hσ
    rw [List.flatten_cons, List.mem_append, not_or] at hnh
    obtain ⟨hnO, hnrest⟩ := hnh
    have hOWF : WFStep O := hWF O List.mem_cons_self
    have hfix : idxOf w (applyStep O μ') = idxOf w μ' :=
      applyStep_idxOf_notMem_husband hOWF hμ' hw hnO
    rw [List.scanl_cons] at hσ
    rcases List.mem_cons.1 hσ with rfl | hσ'
    · rfl
    · have hp' : (applyStep O μ').Perm idRow6 := applyStep_perm hOWF hμ'
      have hnh' : idxOf w (applyStep O μ') ∉ rest.flatten := by rw [hfix]; exact hnrest
      have hrec := ih (applyStep O μ') (fun st hst => hWF st (List.mem_cons_of_mem _ hst))
        hp' hw hnh' σ hσ'
      rw [hrec, hfix]

/-! ## Woman column block destutter -/

theorem foldl_idxOf_notMem :
    ∀ (L : List (List Nat)) (μ' : List Nat), (∀ st ∈ L, WFStep st) →
    μ'.Perm idRow6 → {w : Nat} → w < 6 → idxOf w μ' ∉ L.flatten →
    idxOf w (L.foldl (fun mu st => applyStep st mu) μ') = idxOf w μ' := by
  intro L
  induction L with
  | nil => intro μ' _ _ w _ _; rfl
  | cons O rest ih =>
    intro μ' hWF hμ' w hw hnh
    rw [List.flatten_cons, List.mem_append, not_or] at hnh
    obtain ⟨hnO, hnrest⟩ := hnh
    have hOWF : WFStep O := hWF O List.mem_cons_self
    have hfix : idxOf w (applyStep O μ') = idxOf w μ' :=
      applyStep_idxOf_notMem_husband hOWF hμ' hw hnO
    rw [List.foldl_cons,
      ih (applyStep O μ') (fun st hst => hWF st (List.mem_cons_of_mem _ hst))
        (applyStep_perm hOWF hμ') hw (by rw [hfix]; exact hnrest), hfix]

theorem block_woman_col {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) {w : Nat} (hw : w < 6) :
    ∀ (L : List (List Nat)) (μ' : List Nat), OrbAcc μ ν L →
    (∀ y ∈ L.flatten, μ'.getD y 0 = μ.getD y 0) → μ'.Perm idRow6 →
    ((List.scanl (fun mu st => applyStep st mu) μ' L).map
      (fun σ => idxOf w σ)).destutter (· ≠ ·)
      = if idxOf w μ' ∈ L.flatten
        then [idxOf w μ',
          idxOf w (L.foldl (fun mu st => applyStep st mu) μ')]
        else [idxOf w μ'] := by
  intro L
  induction L with
  | nil =>
    intro μ' _ _ _
    simp [List.scanl_nil]
  | cons O rest ih =>
    intro μ' hOrb hagree hμ'
    obtain ⟨horbs, hdisj⟩ := hOrb
    obtain ⟨m0, hm06, hmov, hOdef⟩ := horbs O List.mem_cons_self
    have hOWF : WFStep O := by
      rw [hOdef]; exact orbit_WFStep hpμ hpν hm06 hmov
    have hOrbRest : OrbAcc μ ν rest :=
      ⟨fun st hst => horbs st (List.mem_cons_of_mem _ hst), hdisj.of_cons⟩
    have hdisjO : ∀ z ∈ O, ∀ t ∈ rest, z ∉ t :=
      fun z hz t ht => (List.pairwise_cons.1 hdisj).1 t ht z hz
    have hWFrest : ∀ st ∈ rest, WFStep st := fun st hst =>
      orbAcc_all_WFStep hpμ hpν hOrbRest st hst
    have hagree' : ∀ y ∈ rest.flatten,
        (applyStep O μ').getD y 0 = μ.getD y 0 := by
      intro y hy
      have hy6 : y < 6 := orbAcc_flatten_lt6 hpμ hpν hOrbRest hy
      have hynO : y ∉ O := by
        intro hyO
        obtain ⟨t, ht, hyt⟩ := List.mem_flatten.1 hy
        exact hdisjO y hyO t ht hyt
      rw [applyStep_getD_notMem hy6 hynO]
      obtain ⟨t, ht, hyt⟩ := List.mem_flatten.1 hy
      exact hagree y (List.mem_flatten.2 ⟨t,
        List.mem_cons_of_mem _ ht, hyt⟩)
    rw [List.scanl_cons, List.map_cons, List.foldl_cons]
    by_cases hhO : idxOf w μ' ∈ O
    · -- husband moves: jumps to h ∈ O, stays through rest
      have hnew : idxOf w (applyStep O μ') ∈ O :=
        applyStep_idxOf_mem_husband hOWF hμ' hw hhO
      have hnnrest : idxOf w (applyStep O μ') ∉ rest.flatten := by
        intro hc
        obtain ⟨t, ht, hmt⟩ := List.mem_flatten.1 hc
        exact hdisjO _ hnew t ht hmt
      have hp' : (applyStep O μ').Perm idRow6 := applyStep_perm hOWF hμ'
      have hconst : ∀ σ ∈ List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest, idxOf w σ = idxOf w (applyStep O μ') :=
        fun σ hσ => scanl_idxOf_notMem_husband rest (applyStep O μ')
          hWFrest hp' hw hnnrest σ hσ
      have hfoldval : idxOf w (rest.foldl (fun mu st => applyStep st mu)
          (applyStep O μ')) = idxOf w (applyStep O μ') :=
        foldl_idxOf_notMem rest (applyStep O μ') hWFrest hp' hw hnnrest
      -- the moved husband is different from the old one
      have hane : idxOf w μ' ≠ idxOf w (applyStep O μ') := by
        intro he
        have hνa0 : (applyStep O μ').getD (idxOf w μ') 0
            = ν.getD (idxOf w μ') 0 := by
          rw [hOdef]
          exact applyStep_orbit_moved' hpμ hpν hm06
            (fun y hy => hagree y (List.mem_flatten.2
              ⟨O, List.mem_cons_self, hOdef ▸ hy⟩))
            (hOdef ▸ hhO) (idxOf_lt6 hμ' hw)
        have hwa : (applyStep O μ').getD (idxOf w μ') 0 = w := by
          rw [he]; exact getD_idxOf (perm6_mem hp' hw)
        have hνw : ν.getD (idxOf w μ') 0 = w := hνa0.symm.trans hwa
        have hmoved : μ.getD (idxOf w μ') 0 ≠ ν.getD (idxOf w μ') 0 :=
          orbit_all_moved hpμ hpν hm06 hmov _ (hOdef ▸ hhO)
        have hwmu : w = μ.getD (idxOf w μ') 0 := by
          rw [← hagree (idxOf w μ') (List.mem_flatten.2
            ⟨O, List.mem_cons_self, hhO⟩)]
          exact (getD_idxOf (perm6_mem hμ' hw)).symm
        exact hmoved (hνw.trans hwmu).symm
      -- tail column = replicate of the new husband
      have htaileq : (List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).map (fun σ => idxOf w σ)
          = List.replicate ((List.scanl (fun mu st => applyStep st mu)
              (applyStep O μ') rest).length) (idxOf w (applyStep O μ')) := by
        rw [List.eq_replicate_iff]
        refine ⟨by rw [List.length_map], ?_⟩
        intro b hb
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hb
        exact hconst σ hσ
      obtain ⟨k, hk⟩ : ∃ k, (List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).length = k + 1 := by
        obtain ⟨T, hT⟩ := scanl_eq_cons (fun mu st => applyStep st mu)
          (applyStep O μ') rest
        exact ⟨T.length, by rw [hT]; simp⟩
      rw [htaileq, hk, destutter_ne_cons_replicate k hane,
        hfoldval, if_pos (List.mem_flatten.2 ⟨O, List.mem_cons_self, hhO⟩)]
    · -- husband fixed by this orbit: leading dup collapses
      have hfix : idxOf w (applyStep O μ') = idxOf w μ' :=
        applyStep_idxOf_notMem_husband hOWF hμ' hw hhO
      have hp' : (applyStep O μ').Perm idRow6 := applyStep_perm hOWF hμ'
      obtain ⟨T, hT⟩ := scanl_eq_cons (fun mu st => applyStep st mu)
        (applyStep O μ') rest
      have hcolM : (List.scanl (fun mu st => applyStep st mu)
          (applyStep O μ') rest).map (fun σ => idxOf w σ)
          = idxOf w μ' :: T.map (fun σ => idxOf w σ) := by
        rw [hT, List.map_cons, hfix]
      rw [hcolM, destutter_ne_dup, ← hcolM,
        ih (applyStep O μ') hOrbRest hagree' hp', hfix]
      by_cases hmr : idxOf w μ' ∈ rest.flatten
      · rw [if_pos hmr, if_pos (List.mem_flatten.2 (by
          obtain ⟨t, ht, hmt⟩ := List.mem_flatten.1 hmr
          exact ⟨t, List.mem_cons_of_mem _ ht, hmt⟩))]
      · rw [if_neg hmr, if_neg (by
          rw [List.flatten_cons, List.mem_append]
          exact fun h => hmr (h.resolve_left hhO))]

/-- Woman-column block destutter in `κ`-form. -/
theorem block_woman_kappa {μ ν : List Nat} (hpμ : μ.Perm idRow6)
    (hpν : ν.Perm idRow6) {w : Nat} (hw : w < 6) :
    ((List.scanl (fun mu st => applyStep st mu) μ
      (stepDecomp μ ν)).map (fun σ => idxOf w σ)).destutter (· ≠ ·)
      = if idxOf w μ ≠ idxOf w ν
        then [idxOf w μ, idxOf w ν] else [idxOf w μ] := by
  have ha6 : idxOf w μ < 6 := idxOf_lt6 hpμ hw
  have hcond : idxOf w μ ∈ (stepDecomp μ ν).flatten
      ↔ idxOf w μ ≠ idxOf w ν := by
    rw [stepDecomp_flatten_iff_moved hpμ hpν ha6,
      getD_idxOf (perm6_mem hpμ hw)]
    constructor
    · intro h he
      apply h
      rw [he]
      exact (getD_idxOf (perm6_mem hpν hw)).symm
    · intro h hc
      exact h (partner_idxOf_of_eq hpν ha6 hc.symm).symm
  rw [block_woman_col hpμ hpν hw (stepDecomp μ ν) μ
    (stepDecomp_spec hpμ hpν).1 (fun y _ => rfl) hpμ,
    foldl_stepDecomp_eq hpμ hpν]
  by_cases hc : idxOf w μ ∈ (stepDecomp μ ν).flatten
  · rw [if_pos hc, if_pos (hcond.1 hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hcond.2 h))]

/-- **The schedule realizes the chain trajectories** (woman side). -/
theorem strajW_eq_wtraj {I : Inst6} (hWF : WF6 I = true) (hne : sms6 I ≠ [])
    (hmo : manOpt I = idRow6) {w : Nat} (hw : w < 6) :
    strajW (chainSched I) w = wtraj I w := by
  obtain ⟨hMmem, _⟩ := manOpt_spec hWF hne
  have hhead : (theChain I).head? = some (manOpt I) :=
    chainFrom_head I 31 (manOpt I)
  have hchain : theChain I = idRow6 :: (theChain I).tail := by
    have h := list_eq_head_tail hhead
    rwa [hmo] at h
  have hpid : idRow6.Perm idRow6 := List.Perm.refl _
  have hptail : ∀ mu ∈ (theChain I).tail, mu.Perm idRow6 :=
    fun mu hmu => chain_mem_perm hWF hne (List.mem_of_mem_tail hmu)
  have hkey := col_destutter_link_gen (fun σ => idxOf w σ)
    (fun μ ν hpμ hpν => block_woman_kappa hpμ hpν hw)
    (theChain I).tail idRow6 hpid hptail
  unfold strajW chainSched schedMatchings wtraj
  conv_lhs => rw [hchain]
  rw [hkey, ← hchain]
