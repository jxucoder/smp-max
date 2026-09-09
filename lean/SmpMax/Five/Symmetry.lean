import SmpMax.Five.Definitions

/-!
# Symmetry reduction: relabeling women by man 0's ranking

`relabel I` renames woman `w` to `σ w` where `σ` is man 0's rank row.
After relabeling, man 0's rank row is the identity, well-formedness is
preserved, and the stable-matching count is unchanged — which yields
`reduce_man0'`.
-/

/-- Function view of a rank row / permutation list. -/
def app (l : List Nat) (w : Nat) : Nat := l.getD w 0

/-- Inverse of a length-5 permutation list. -/
def invList (σ : List Nat) : List Nat := (List.range 5).map (fun v => idxOf v σ)

def sigma (I : Inst) : List Nat := I.mrank.getD 0 []

def relabel (I : Inst) : Inst where
  mrank := I.mrank.map fun row =>
    (List.range 5).map fun w' => row.getD (app (invList (sigma I)) w') 0
  wrank := (List.range 5).map fun w' =>
    I.wrank.getD (app (invList (sigma I)) w') []

/-! ## idxOf lemmas -/

theorem idxOf_lt_length {x : Nat} {l : List Nat} (h : x ∈ l) :
    idxOf x l < l.length := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [idxOf, List.length_cons]
    split
    · omega
    · next hy =>
      have hx : x ∈ ys := by
        rcases List.mem_cons.1 h with h1 | h1
        · exact absurd h1.symm hy
        · exact h1
      have := ih hx
      omega

theorem getD_idxOf {x : Nat} {l : List Nat} (h : x ∈ l) :
    l.getD (idxOf x l) 0 = x := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [idxOf]
    split
    · next hy => rw [List.getD_cons_zero]; exact hy
    · next hy =>
      have hx : x ∈ ys := by
        rcases List.mem_cons.1 h with h1 | h1
        · exact absurd h1.symm hy
        · exact h1
      rw [List.getD_cons_succ]
      exact ih hx

theorem idxOf_getD {l : List Nat} (hnd : l.Nodup) :
    ∀ {i : Nat}, i < l.length → idxOf (l.getD i 0) l = i := by
  induction l with
  | nil => intro i h; simp at h
  | cons y ys ih =>
    intro i h
    match i with
    | 0 => rw [List.getD_cons_zero]; simp [idxOf]
    | j + 1 =>
      have hj : j < ys.length := by simpa using h
      have hnd' := List.nodup_cons.1 hnd
      have hmem : ys.getD j 0 ∈ ys := by
        rw [List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hne : ¬(y = ys.getD j 0) := fun hc => hnd'.1 (hc ▸ hmem)
      rw [List.getD_cons_succ]
      simp only [idxOf, if_neg hne]
      rw [ih hnd'.2 hj]

theorem idxOf_map {f : Nat → Nat} {x : Nat} {l : List Nat}
    (hinj : ∀ y ∈ l, f y = f x → y = x) :
    idxOf (f x) (l.map f) = idxOf x l := by
  induction l with
  | nil => simp [idxOf]
  | cons y ys ih =>
    simp only [List.map_cons, idxOf]
    by_cases hy : y = x
    · subst hy; simp
    · have hfy : ¬(f y = f x) := fun hc => hy (hinj y (by simp) hc)
      rw [if_neg hfy, if_neg hy, ih fun z hz => hinj z (by simp [hz])]

/-! ## Facts about σ and its inverse -/

theorem idRow_eq_range : idRow = List.range 5 := by decide

theorem map_getD_range {l : List Nat} (h : l.length = 5) :
    (List.range 5).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem h2]

theorem getD_map_lt {f : List Nat → List Nat} {l : List (List Nat)} {i : Nat}
    (h : i < l.length) : (l.map f).getD i [] = f (l.getD i []) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map,
      List.getD_eq_getElem _ _ h]

theorem sigma_length {σ : List Nat} (hp : σ.Perm idRow) : σ.length = 5 := by
  have := hp.length_eq
  simpa [idRow] using this

theorem sigma_nodup {σ : List Nat} (hp : σ.Perm idRow) : σ.Nodup :=
  hp.nodup_iff.2 (by decide)

theorem sigma_mem {σ : List Nat} (hp : σ.Perm idRow) {v : Nat} (hv : v < 5) :
    v ∈ σ := by
  rw [hp.mem_iff, idRow_eq_range]
  simpa using hv

theorem sigma_app_lt {σ : List Nat} (hp : σ.Perm idRow) {w : Nat} (hw : w < 5) :
    app σ w < 5 := by
  have hlt : w < σ.length := by rw [sigma_length hp]; exact hw
  have hmem : σ.getD w 0 ∈ σ := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  have h2 : σ.getD w 0 ∈ idRow := hp.mem_iff.1 hmem
  rw [idRow_eq_range] at h2
  simpa [app] using h2

theorem inv_app {σ : List Nat} {v : Nat} (hv : v < 5) :
    app (invList σ) v = idxOf v σ := by
  have hlt : v < ((List.range 5).map (fun v => idxOf v σ)).length := by simpa using hv
  simp only [invList, app]
  rw [List.getD_eq_getElem _ _ hlt]
  simp

theorem inv_app_app {σ : List Nat} (hp : σ.Perm idRow) {w : Nat} (hw : w < 5) :
    app (invList σ) (app σ w) = w := by
  rw [inv_app (sigma_app_lt hp hw)]
  exact idxOf_getD (sigma_nodup hp) (by rw [sigma_length hp]; exact hw)

theorem app_inv_app {σ : List Nat} (hp : σ.Perm idRow) {v : Nat} (hv : v < 5) :
    app σ (app (invList σ) v) = v := by
  rw [inv_app hv]
  exact getD_idxOf (sigma_mem hp hv)

theorem inv_app_lt {σ : List Nat} (hp : σ.Perm idRow) {v : Nat} (hv : v < 5) :
    app (invList σ) v < 5 := by
  rw [inv_app hv]
  have := idxOf_lt_length (sigma_mem hp hv)
  rw [sigma_length hp] at this
  exact this

/-! ## σ from a well-formed instance -/

theorem WF_unfold {I : Inst} (h : WF I = true) :
    I.mrank.length = 5 ∧ I.wrank.length = 5 ∧
    (∀ r ∈ I.mrank, isRankRow r = true) ∧
    (∀ r ∈ I.wrank, isRankRow r = true) := by
  simp only [WF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem sigma_perm {I : Inst} (h : WF I = true) : (sigma I).Perm idRow := by
  obtain ⟨hm, _, hrows, _⟩ := WF_unfold h
  have h0lt : 0 < I.mrank.length := by omega
  apply rankRow_perm
  rw [sigma, List.getD_eq_getElem _ _ h0lt]
  exact hrows _ (List.getElem_mem h0lt)

/-! ## relabel fixes man 0 -/

theorem relabel_man0 {I : Inst} (h : WF I = true) :
    (relabel I).mrank.getD 0 [] = idRow := by
  obtain ⟨hm, _, _, _⟩ := WF_unfold h
  have hp := sigma_perm h
  have hmap : (relabel I).mrank.getD 0 [] =
      (List.range 5).map fun w' => app (sigma I) (app (invList (sigma I)) w') := by
    simp only [relabel]
    rw [getD_map_lt (show 0 < I.mrank.length by omega)]
    rfl
  rw [hmap, idRow_eq_range]
  have hcongr : ∀ w' ∈ List.range 5,
      app (sigma I) (app (invList (sigma I)) w') = id w' := by
    intro w' hw'
    exact app_inv_app hp (by simpa using hw')
  rw [List.map_congr_left hcongr, List.map_id]

theorem getD_map_range {f : Nat → Nat} {w : Nat} (hw : w < 5) :
    ((List.range 5).map f).getD w 0 = f w := by
  have hlt : w < ((List.range 5).map f).length := by simpa using hw
  rw [List.getD_eq_getElem _ _ hlt]
  simp

theorem relabel_WF {I : Inst} (h : WF I = true) : WF (relabel I) = true := by
  obtain ⟨hm, hw, hmrows, hwrows⟩ := WF_unfold h
  have hp := sigma_perm h
  simp only [WF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, relabel]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp [hm]
  · simp
  · intro r hr
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hr
    have hrr := hmrows _ hrow
    simp only [isRankRow, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hrr ⊢
    obtain ⟨hlen, hcont⟩ := hrr
    refine ⟨by simp, ?_⟩
    intro v hv
    have hv5 : v < 5 := by simpa using hv
    have hvrow : v ∈ row := by
      have := hcont v hv
      simpa [List.contains_iff_mem] using this
    have hidx5 : idxOf v row < 5 := by
      have := idxOf_lt_length hvrow
      rw [hlen] at this
      exact this
    have hw' : app (sigma I) (idxOf v row) < 5 := sigma_app_lt hp hidx5
    have hval : ((List.range 5).map fun w' =>
        row.getD (app (invList (sigma I)) w') 0).getD (app (sigma I) (idxOf v row)) 0 = v := by
      rw [getD_map_range hw', inv_app_app hp hidx5]
      exact getD_idxOf hvrow
    have hlen' : app (sigma I) (idxOf v row) < ((List.range 5).map fun w' =>
        row.getD (app (invList (sigma I)) w') 0).length := by simpa using hw'
    have hmem : v ∈ ((List.range 5).map fun w' =>
        row.getD (app (invList (sigma I)) w') 0) := by
      rw [← hval, List.getD_eq_getElem _ _ hlen']
      exact List.getElem_mem hlen'
    simpa [List.contains_iff_mem] using hmem
  · intro r hr
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hr
    have hw5 : w' < 5 := by simpa using hw'
    have hinv5 : app (invList (sigma I)) w' < 5 := inv_app_lt hp hw5
    have hlt : app (invList (sigma I)) w' < I.wrank.length := by
      rw [hw]; exact hinv5
    rw [List.getD_eq_getElem _ _ hlt]
    exact hwrows _ (List.getElem_mem hlt)

/-! ## Stability and counting are preserved (the core bijection) -/

theorem getD_map_range' {α : Type} {d : α} {f : Nat → α} {w : Nat} (hw : w < 5) :
    ((List.range 5).map f).getD w d = f w := by
  have hlt : w < ((List.range 5).map f).length := by simpa using hw
  rw [List.getD_eq_getElem _ _ hlt]
  simp

theorem getD_map_nat {f : Nat → Nat} {l : List Nat} {i : Nat} (h : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map,
      List.getD_eq_getElem _ _ h]

theorem invList_isRankRow {σ : List Nat} (hp : σ.Perm idRow) :
    isRankRow (invList σ) = true := by
  simp only [isRankRow, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨by simp [invList], ?_⟩
  intro v hv
  have hv5 : v < 5 := by simpa using hv
  have hpos : app σ v < 5 := sigma_app_lt hp hv5
  have hlt : app σ v < (invList σ).length := by
    simp only [invList, List.length_map, List.length_range]
    exact hpos
  have hval : (invList σ).getD (app σ v) 0 = v := inv_app_app hp hv5
  have hmem : v ∈ invList σ := by
    rw [← hval, List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  simpa [List.contains_iff_mem] using hmem

theorem invList_perm {σ : List Nat} (hp : σ.Perm idRow) :
    (invList σ).Perm idRow := rankRow_perm (invList_isRankRow hp)

theorem entry_lt {l : List Nat} (hmu : l.Perm idRow)
    {y : Nat} (hy : y ∈ l) : y < 5 := by
  have : y ∈ idRow := hmu.mem_iff.1 hy
  rw [idRow_eq_range] at this
  simpa using this

theorem map_app_left_inv {σ mu : List Nat} (hp : σ.Perm idRow)
    (hmu : mu.Perm idRow) :
    (mu.map (app σ)).map (app (invList σ)) = mu := by
  rw [List.map_map]
  have hc : ∀ x ∈ mu, (app (invList σ) ∘ app σ) x = id x := by
    intro x hx
    simpa using inv_app_app hp (entry_lt hmu hx)
  rw [List.map_congr_left hc, List.map_id]

theorem map_app_right_inv {σ mu' : List Nat} (hp : σ.Perm idRow)
    (hmu : mu'.Perm idRow) :
    (mu'.map (app (invList σ))).map (app σ) = mu' := by
  rw [List.map_map]
  have hc : ∀ x ∈ mu', (app σ ∘ app (invList σ)) x = id x := by
    intro x hx
    simpa using app_inv_app hp (entry_lt hmu hx)
  rw [List.map_congr_left hc, List.map_id]

theorem mapMu_mem {σ mu : List Nat} (hp : σ.Perm idRow)
    (hmu : mu ∈ ([0, 1, 2, 3, 4] : List Nat).permutations) :
    mu.map (app σ) ∈ ([0, 1, 2, 3, 4] : List Nat).permutations := by
  have hmup : mu.Perm idRow := List.mem_permutations.1 hmu
  apply List.mem_permutations.2
  have h1 : (mu.map (app σ)).Perm (idRow.map (app σ)) := hmup.map _
  have h2 : idRow.map (app σ) = σ := by
    rw [idRow_eq_range]
    exact map_getD_range (sigma_length hp)
  rw [h2] at h1
  exact h1.trans hp

theorem perms_map_perm {σ : List Nat} (hp : σ.Perm idRow) :
    (([0, 1, 2, 3, 4] : List Nat).permutations.map
      (fun mu => mu.map (app σ))).Perm
    ([0, 1, 2, 3, 4] : List Nat).permutations := by
  have hnd : ([0, 1, 2, 3, 4] : List Nat).permutations.Nodup :=
    List.nodup_permutations _ (by decide)
  have hndm : (([0, 1, 2, 3, 4] : List Nat).permutations.map
      (fun mu => mu.map (app σ))).Nodup := by
    refine List.Nodup.map_on ?_ hnd
    intro mu1 h1 mu2 h2 heq
    have hc := congrArg (List.map (app (invList σ))) heq
    rwa [map_app_left_inv hp (List.mem_permutations.1 h1),
        map_app_left_inv hp (List.mem_permutations.1 h2)] at hc
  rw [List.perm_ext_iff_of_nodup hndm hnd]
  intro mu'
  constructor
  · intro hmem
    obtain ⟨mu, hmu, rfl⟩ := List.mem_map.1 hmem
    exact mapMu_mem hp hmu
  · intro hmem
    refine List.mem_map.2 ⟨mu'.map (app (invList σ)), ?_, ?_⟩
    · exact mapMu_mem (invList_perm hp) hmem
    · exact map_app_right_inv hp (List.mem_permutations.1 hmem)

theorem get2_relabel_m {I : Inst} (h : WF I = true) {m x : Nat}
    (hm : m < 5) (hx : x < 5) :
    get2 (relabel I).mrank m x = get2 I.mrank m (app (invList (sigma I)) x) := by
  obtain ⟨hml, _, _, _⟩ := WF_unfold h
  simp only [get2, relabel]
  rw [getD_map_lt (show m < I.mrank.length by omega), getD_map_range' hx]

theorem get2_relabel_w {I : Inst} (h : WF I = true) {x : Nat} (hx : x < 5)
    (m : Nat) :
    get2 (relabel I).wrank x m = get2 I.wrank (app (invList (sigma I)) x) m := by
  simp only [get2, relabel]
  rw [getD_map_range' (d := ([] : List Nat)) hx]

theorem body_shift {I : Inst} (h : WF I = true) {mu : List Nat}
    (hmu : mu.Perm idRow) {m w : Nat} (hm : m < 5) (hw : w < 5) :
    ((app (sigma I) w = (mu.map (app (sigma I))).getD m 0) ∨
      ¬get2 (relabel I).mrank m (app (sigma I) w) <
          get2 (relabel I).mrank m ((mu.map (app (sigma I))).getD m 0) ∨
      ¬get2 (relabel I).wrank (app (sigma I) w) m <
          get2 (relabel I).wrank (app (sigma I) w)
            (idxOf (app (sigma I) w) (mu.map (app (sigma I))))) ↔
    ((w = mu.getD m 0) ∨
      ¬get2 I.mrank m w < get2 I.mrank m (mu.getD m 0) ∨
      ¬get2 I.wrank w m < get2 I.wrank w (idxOf w mu)) := by
  have hp := sigma_perm h
  have hmlen : m < mu.length := by rw [sigma_length hmu]; exact hm
  have hwm5 : mu.getD m 0 < 5 := sigma_app_lt hmu hm
  have hidx : idxOf (app (sigma I) w) (mu.map (app (sigma I))) = idxOf w mu := by
    refine idxOf_map ?_
    intro y hy hxy
    have hc := congrArg (app (invList (sigma I))) hxy
    rwa [inv_app_app hp (entry_lt hmu hy), inv_app_app hp hw] at hc
  have heq : (app (sigma I) w = app (sigma I) (mu.getD m 0)) ↔
      (w = mu.getD m 0) := by
    constructor
    · intro he
      have hc := congrArg (app (invList (sigma I))) he
      rwa [inv_app_app hp hw, inv_app_app hp hwm5] at hc
    · intro he; rw [he]
  rw [getD_map_nat hmlen, hidx,
      get2_relabel_m h hm (sigma_app_lt hp hw),
      get2_relabel_m h hm (sigma_app_lt hp hwm5),
      get2_relabel_w h (sigma_app_lt hp hw) m,
      get2_relabel_w h (sigma_app_lt hp hw) (idxOf w mu),
      inv_app_app hp hw, inv_app_app hp hwm5, heq]

theorem isStable_relabel {I : Inst} (h : WF I = true) {mu : List Nat}
    (hmu : mu.Perm idRow) :
    isStable (relabel I) (mu.map (app (sigma I))) = isStable I mu := by
  have hp := sigma_perm h
  rw [Bool.eq_iff_iff]
  simp only [isStable, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · intro H m hm w hw
    have hkey := H m hm (app (sigma I) w) (sigma_app_lt hp hw)
    exact (body_shift h hmu hm hw).1 hkey
  · intro H m hm w'' hw''
    have hw : app (invList (sigma I)) w'' < 5 := inv_app_lt hp hw''
    have hkey := (body_shift h hmu hm hw).2 (H m hm _ hw)
    rwa [app_inv_app hp hw''] at hkey

theorem stableCount_relabel {I : Inst} (h : WF I = true) :
    stableCount (relabel I) = stableCount I := by
  have hp := sigma_perm h
  unfold stableCount
  have h1 : (([0, 1, 2, 3, 4] : List Nat).permutations.filter
        (isStable (relabel I))).length
      = ((([0, 1, 2, 3, 4] : List Nat).permutations.map
          (fun mu => mu.map (app (sigma I)))).filter
            (isStable (relabel I))).length :=
    (((perms_map_perm hp).filter _).length_eq).symm
  rw [h1, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro mu hmu
  exact isStable_relabel h (List.mem_permutations.1 hmu)

/-- **Symmetry step (target)**: it suffices to bound instances whose man 0
has the identity ranking. -/
theorem reduce_man0'
    (h : ∀ I : Inst, WF I = true → I.mrank.getD 0 [] = idRow →
         stableCount I ≤ 16) :
    ∀ I : Inst, WF I = true → stableCount I ≤ 16 := by
  intro I hWF
  rw [← stableCount_relabel hWF]
  exact h _ (relabel_WF hWF) (relabel_man0 hWF)
