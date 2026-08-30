import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD

/-!
# Layer 2 scaffold: f(5) ≤ 16 in Lean

Generalizes `Witness.lean`'s concrete computation to arbitrary well-formed
5×5 instances, and states the theorems whose proofs constitute the
remaining formalization work. Proof architecture (option B):

  f5_upper
    ⟵ reduce_man0 (symmetry: WLOG man 0's ranking is the identity)
    ⟵ cube_covering (man 1's ranking is one of the 120 permutations)
    ⟵ per-cube faithfulness + cake_lpr-verified UNSAT certificates
      (the certificate step lives outside Lean's kernel, checked by the
       formally verified cake_lpr; Lean states the bridge explicitly).
-/

/-- A 5×5 stable-marriage instance as rank tables:
`mrank[m][w]` = position of woman `w` in man `m`'s preference order
(0 = most preferred); `wrank[w][m]` symmetric. -/
structure Inst where
  mrank : List (List Nat)
  wrank : List (List Nat)
deriving Repr

def isRankRow (r : List Nat) : Bool :=
  r.length = 5 && (List.range 5).all fun v => r.contains v

/-- Well-formed: both tables are 5 rows, each row a permutation of 0..4. -/
def WF (I : Inst) : Bool :=
  I.mrank.length = 5 && I.wrank.length = 5 &&
  I.mrank.all isRankRow && I.wrank.all isRankRow

def get2 (t : List (List Nat)) (i j : Nat) : Nat := (t.getD i []).getD j 0

def idxOf (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => if y = x then 0 else idxOf x ys + 1

def isStable (I : Inst) (mu : List Nat) : Bool :=
  (List.range 5).all fun m =>
    (List.range 5).all fun w =>
      let wm := mu.getD m 0
      let mw := idxOf w mu
      (w = wm) ||
      !(get2 I.mrank m w < get2 I.mrank m wm &&
        get2 I.wrank w m < get2 I.wrank w mw)

def stableCount (I : Inst) : Nat :=
  (([0, 1, 2, 3, 4] : List Nat).permutations.filter (isStable I)).length

/-- The identity rank row: man ranks woman `w` at position `w`. -/
def idRow : List Nat := [0, 1, 2, 3, 4]

/-- A well-formed rank row is a permutation of `idRow`. -/
theorem rankRow_perm {r : List Nat} (h : isRankRow r = true) :
    r.Perm idRow := by
  simp only [isRankRow, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hmem⟩ := h
  have hsub : idRow ⊆ r := by
    intro v hv
    have hv5 : v < 5 := by
      simp only [idRow, List.mem_cons, List.not_mem_nil, or_false] at hv
      omega
    have := hmem v (by simpa using hv5)
    simpa [List.contains_iff_mem] using this
  have hnd : idRow.Nodup := by decide
  have hsp : idRow.Subperm r := hnd.subperm hsub
  have hlen' : r.length ≤ idRow.length := by simp [hlen, idRow]
  exact (hsp.perm_of_length_le hlen').symm

/-- **Covering step** (proved): with man 0 fixed, man 1's rank row is one of
the 120 permutations of 0..4 — i.e. the cubes of `cube_run.py` exhaust all
cases. `idRow.permutations` is a concrete 120-element list. -/
theorem cube_covering (I : Inst) (h : WF I = true) :
    I.mrank.getD 1 [] ∈ idRow.permutations := by
  simp only [WF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hm, _⟩, hrows⟩, _⟩ := h
  have h1lt : 1 < I.mrank.length := by rw [hm]; omega
  have h1 : isRankRow (I.mrank.getD 1 []) = true := by
    rw [List.getD_eq_getElem _ _ h1lt]
    exact hrows _ (List.getElem_mem h1lt)
  exact List.mem_permutations.2 (rankRow_perm h1)

/-- **Per-cube bridge** (one statement per cube i ∈ 0..119, schematically):
if `WF I`, man 0 = idRow, man 1 = cube i's order, and `stableCount I ≥ 17`,
then the assignment read off `I` satisfies cube i's CNF — whose
unsatisfiability is certified by cake_lpr. Formal statement to be
instantiated once the Lean-side CNF builder mirrors `encode.py`. -/
theorem faithfulness_placeholder : True := trivial
