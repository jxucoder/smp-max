import SmpF5.Faithful

/-!
# The cube CNFs, defined in Lean (single source of truth)

For cube `row` (a candidate rank row for man 1), `cubeCNF row` is
satisfiable iff ... — the faithfulness direction we prove is:
any well-formed instance with man 0 = idRow, man 1's rank row = `row`,
and ≥ 17 stable matchings yields a satisfying assignment.

Encoding ("selector" style, chosen for formalizability):
- pref vars: `prefVar side i (a,b)` for a<b — "person i on side prefers
  a over b" (side 0 = men, 1 = women); ids 1..100.
- selector vars `yVar t μi` (t ∈ 0..16, μi ∈ 0..119): "slot t selects the
  μi-th permutation of `perms120`"; ids 101..2140.
- clauses: preference transitivity; unit fixes for man 0 (identity) and
  man 1 (`row`); each slot nonempty; consecutive slots strictly
  increasing in μi (kills slot symmetry, forces 17 distinct selections);
  a selected matching admits no blocking pair.

The DIMACS files consumed by kissat / drat-trim / cake_lpr are printed
from these very definitions by `export_cnf` (Main.lean).
-/

def perms120 : List (List Nat) := idRow.permutations

def pairs5 : List (Nat × Nat) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def triples5 : List (Nat × Nat × Nat) :=
  [(0,1,2),(0,1,3),(0,1,4),(0,2,3),(0,2,4),(0,3,4),(1,2,3),(1,2,4),(1,3,4),(2,3,4)]

/-- Index of pair (a,b), a<b, in `pairs5`. -/
def pidx (a b : Nat) : Nat := (a * (9 - a)) / 2 + b - a - 1

def prefVar (side i a b : Nat) : Nat := 1 + side * 50 + i * 10 + pidx a b

/-- Literal for "person i on side prefers a over b" (any a ≠ b). -/
def prefLit (side i a b : Nat) : Int :=
  if a < b then Int.ofNat (prefVar side i a b)
  else -(Int.ofNat (prefVar side i b a))

def yVar (t μi : Nat) : Nat := 101 + t * 120 + μi

def yLit (t μi : Nat) : Int := Int.ofNat (yVar t μi)

def transClauses : List (List Int) :=
  (List.range 2).flatMap fun side =>
    (List.range 5).flatMap fun i =>
      triples5.flatMap fun (a, b, c) =>
        [[-(prefLit side i a b), -(prefLit side i b c), prefLit side i a c],
         [prefLit side i a b, prefLit side i b c, -(prefLit side i a c)]]

def man0Units : List (List Int) :=
  pairs5.map fun (a, b) => [prefLit 0 0 a b]

/-- Man 1's rank row is `row`: he prefers a over b iff row[a] < row[b]. -/
def man1Units (row : List Nat) : List (List Int) :=
  pairs5.map fun (a, b) =>
    [if row.getD a 0 < row.getD b 0 then prefLit 0 1 a b else -(prefLit 0 1 a b)]

def nonemptyClausesK (k : Nat) : List (List Int) :=
  (List.range k).map fun t => (List.range 120).map fun μi => yLit t μi

def orderingClausesK (k : Nat) : List (List Int) :=
  (List.range (k - 1)).flatMap fun t =>
    (List.range 120).flatMap fun μi =>
      (List.range (μi + 1)).map fun μj =>
        [-(yLit t μi), -(yLit (t + 1) μj)]

def blockClausesK (k : Nat) : List (List Int) :=
  (List.range k).flatMap fun t =>
    (List.range 120).flatMap fun μi =>
      let mu := perms120.getD μi []
      (List.range 5).flatMap fun m =>
        (List.range 5).filterMap fun w =>
          if w = mu.getD m 0 then none
          else some [-(yLit t μi),
            -(prefLit 0 m w (mu.getD m 0)),
            -(prefLit 1 w m (idxOf w mu))]

def cubeCNFK (k : Nat) (row : List Nat) : List (List Int) :=
  transClauses ++ man0Units ++ man1Units row ++
  nonemptyClausesK k ++ orderingClausesK k ++ blockClausesK k

/-- The production formula: 17 slots. -/
def cubeCNF (row : List Nat) : List (List Int) := cubeCNFK 17 row

/-- Positive-control formula: 16 slots (must be satisfiable for a cube
containing a 16-stable-matching instance). -/
def cubeCNF16 (row : List Nat) : List (List Int) := cubeCNFK 16 row

def numVars : Nat := 2140

/-! ## Satisfiability semantics -/

def evalLit (τ : Nat → Bool) (l : Int) : Bool :=
  if 0 < l then τ l.toNat else !(τ (-l).toNat)

def evalClause (τ : Nat → Bool) (c : List Int) : Bool := c.any (evalLit τ)

def evalCNF (τ : Nat → Bool) (F : List (List Int)) : Bool :=
  F.all (evalClause τ)

def Satisfiable (F : List (List Int)) : Prop := ∃ τ, evalCNF τ F = true

theorem perms120_length : perms120.length = 120 := by
  rw [perms120, List.length_permutations]
  rfl
