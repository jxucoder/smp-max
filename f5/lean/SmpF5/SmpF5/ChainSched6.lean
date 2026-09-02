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
