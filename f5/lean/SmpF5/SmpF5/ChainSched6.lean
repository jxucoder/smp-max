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
