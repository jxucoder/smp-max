import SmpF5.Encoding

/-!
# The schedule CNF (order 6, target k), defined in Lean

Single source of truth for the f(6) campaign formulas
(docs/history/f6-REPLAY_DESIGN.md, Architecture 3).  `schedCNF k` is, clause for clause
and literal for literal, the formula written by
`f6/sched_sat.py :: build(6, k)`; `cubeCNF k prefix` adds the unit
clauses of `--fix-prefix=` (one unit `S[t][idx(prefix[t]) + 1]` per
prefix step).  The DIMACS files consumed by kissat / drat-trim /
cake_lpr are printed from these definitions by `export_sched_cnf`
(`ExportSchedCnf.lean`), and `export_sched_cnf` output is checked
byte-for-byte against the Python writer.

Every definition below cites the Python code it mirrors.  The structure
is deliberately one-to-one with the Python (nested `List.range` loops,
`flatMap` for `for`, `filterMap` for `for ... if`), so that the
faithfulness proof can follow the encoding literally.

Bounded-model-checking encoding (`sched_sat.py` docstring):
* `F = n(n-1)/2` frames; frame state = one-hot matching `M[t][m][w]`
  and monotone visited masks `V[t][m][w]`;
* per frame a one-hot step choice `S[t][j]`: `j = 0` is "stop",
  `j ≥ 1` is the cyclic shape `SH[j-1]` (`cyclicShapes`);
* first-visit-order auxiliaries `C`, `before`, `neither`, `PM` (men's
  read-off preference) and `beforeW`, `later`, `only_a`, `nv` (the
  per-(w,a,b) bottom term, a<b, allocated inside the `PW` loop), `PW`
  (women's read-off preference, reversed trajectory);
* selector block: `k` slots `Y[t][i]` over the `n!` matchings with a
  ladder `Pf[t][i]` forcing strictly increasing (hence distinct)
  selections; a selected matching admits no blocking pair.

## Variable numbering

The Python allocator (`Enc.new`) hands out ids `1, 2, 3, …` in program
order.  We reproduce that order with explicit offsets, in the same
order the Python allocates:

```
M     : (F+1)·n·n ids           (t, m, w)               -- build: `M = ...`
V     : (F+1)·n·n ids           (t, m, w)               -- `V = ...`
S     : F·(NS+1) ids            (t, j), j=0 is stop     -- `S = ...`
C/bv  : n·n(n-1)·(F+2) ids      (m, a≠b): F+1 c's then bv   -- `before` loop
neither: n·n(n-1)/2 ids         (m, a<b)                -- `neither` loop
PM    : n·n(n-1) ids            (m, a≠b)                -- `PM` loop
CW/bvW: n·n(n-1)·(F+2) ids      (w, a≠b): F+1 c's then bv   -- `beforeW` loop
PW    : n·(7n(n-1)/2) ids       (w, a≠b): p, later, only_a, [nv if a<b] -- `PW` loop
Y     : k·NP ids                (t, i)                  -- `Y = ...`
Pf    : k·NP ids                (t, i)                  -- `Pf = ...`
```
-/

namespace SchedCNF6

/-! ## Combinatorial enumerations, in Python's `itertools` order -/

/-- `itertools.combinations(xs, k)` for a list `xs`: lexicographic in
positions (all combinations containing the head first, then those that
do not). -/
def combos : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | x :: xs, k + 1 => (combos xs k).map (x :: ·) ++ combos xs (k + 1)

/-- All ways to pick one element out of a list, in position order,
paired with the remaining list (order preserved). -/
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map fun (y, ys) => (y, x :: ys)

/-- `itertools.permutations(xs)` order: choose the first element in
position order, then recurse on the rest.  `fuel` is `xs.length`. -/
def permsAux : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | fuel + 1, xs => (picks xs).flatMap fun (y, ys) => (permsAux fuel ys).map (y :: ·)

/-- `list(itertools.permutations(xs))`. -/
def permsOf (xs : List Nat) : List (List Nat) := permsAux xs.length xs

/-- `sched_sat.cyclic_shapes(n)`:
```
for kk in range(2, n + 1):
    for men in itertools.combinations(range(n), kk):
        for rest in itertools.permutations(men[1:]):
            shapes.append((men[0],) + rest)
``` -/
def cyclicShapes (n : Nat) : List (List Nat) :=
  (List.range (n - 1)).flatMap fun kk' =>
    let kk := kk' + 2
    (combos (List.range n) kk).flatMap fun men =>
      (permsOf men.tail).map fun rest => men.headD 0 :: rest

/-- `P = list(itertools.permutations(range(n)))`. -/
def permsN (n : Nat) : List (List Nat) := permsOf (List.range n)

/-! ## Layout: the sizes the Python `build` computes once -/

/-- The sizes fixed at the top of `build(n, k)`:
`F = n*(n-1)//2`, `SH = cyclic_shapes(n)`, `NS = len(SH)`,
`NP = len(P)`. -/
structure Lay where
  n : Nat
  F : Nat
  NS : Nat
  NP : Nat

def layout (n : Nat) : Lay :=
  { n := n, F := n * (n - 1) / 2, NS := (cyclicShapes n).length, NP := (permsN n).length }

/-! ## Variable ids (see the numbering table above) -/

/-- Index of the ordered pair `(a, b)`, `a ≠ b`, in the Python loop
`for a in range(n): for b in range(n): if a == b: continue`. -/
def opIdx (n a b : Nat) : Nat := a * (n - 1) + (if b < a then b else b - 1)

/-- Index of the unordered pair `(a, b)`, `a < b`, in the Python loop
`for a in range(n): for b in range(a+1, n)`. -/
def upIdx (n a b : Nat) : Nat := a * (2 * n - 1 - a) / 2 + b - a - 1

/-- `M[t][m][w]`. -/
def mVar (L : Lay) (t m w : Nat) : Nat := 1 + t * (L.n * L.n) + m * L.n + w

/-- `V[t][m][w]`. -/
def vVar (L : Lay) (t m w : Nat) : Nat :=
  1 + (L.F + 1) * (L.n * L.n) + t * (L.n * L.n) + m * L.n + w

def sBase (L : Lay) : Nat := 1 + 2 * (L.F + 1) * (L.n * L.n)

/-- `S[t][j]` (`j = 0` is stop, `j ≥ 1` is shape `SH[j-1]`). -/
def sVar (L : Lay) (t j : Nat) : Nat := sBase L + t * (L.NS + 1) + j

def beforeBase (L : Lay) : Nat := sBase L + L.F * (L.NS + 1)

/-- The `t`-th auxiliary `c` of `before[(m, a, b)]` (`t ≤ F`). -/
def cVar (L : Lay) (m a b t : Nat) : Nat :=
  beforeBase L + (m * (L.n * (L.n - 1)) + opIdx L.n a b) * (L.F + 2) + t

/-- `before[(m, a, b)]` (allocated right after its `F+1` c's). -/
def beforeVar (L : Lay) (m a b : Nat) : Nat := cVar L m a b (L.F + 1)

def neitherBase (L : Lay) : Nat := beforeBase L + L.n * (L.n * (L.n - 1)) * (L.F + 2)

/-- `neither[(m, a, b)]`, `a < b`. -/
def neitherVar (L : Lay) (m a b : Nat) : Nat :=
  neitherBase L + m * (L.n * (L.n - 1) / 2) + upIdx L.n a b

def pmBase (L : Lay) : Nat := neitherBase L + L.n * (L.n * (L.n - 1) / 2)

/-- `PM[(m, a, b)]`. -/
def pmVar (L : Lay) (m a b : Nat) : Nat := pmBase L + m * (L.n * (L.n - 1)) + opIdx L.n a b

def beforeWBase (L : Lay) : Nat := pmBase L + L.n * (L.n * (L.n - 1))

/-- The `t`-th auxiliary `c` of `beforeW[(w, a, b)]`. -/
def cWVar (L : Lay) (w a b t : Nat) : Nat :=
  beforeWBase L + (w * (L.n * (L.n - 1)) + opIdx L.n a b) * (L.F + 2) + t

/-- `beforeW[(w, a, b)]`. -/
def beforeWVar (L : Lay) (w a b : Nat) : Nat := cWVar L w a b (L.F + 1)

def pwBase (L : Lay) : Nat := beforeWBase L + L.n * (L.n * (L.n - 1)) * (L.F + 2)

/-- The ordered pairs `(a, b)`, `a ≠ b`, in Python loop order. -/
def opairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun a =>
    (List.range n).filterMap fun b => if a = b then none else some (a, b)

/-- Number of ids the `PW` loop allocates for pair `(a, b)`:
`p`, `later`, `only_a`, and `nv` iff `a < b`. -/
def pwWidth (a b : Nat) : Nat := if a < b then 4 else 3

/-- Ids allocated by the `PW` loop for one woman before reaching `(a, b)`. -/
def pwOff (n a b : Nat) : Nat :=
  (((opairs n).takeWhile fun ab => ab != (a, b)).map fun ab => pwWidth ab.1 ab.2).sum

/-- Ids allocated by the `PW` loop per woman (`7n(n-1)/2`). -/
def pwPerW (n : Nat) : Nat := ((opairs n).map fun ab => pwWidth ab.1 ab.2).sum

/-- The `i`-th id of the `PW` group `(w, a, b)`:
`i = 0`: `p = PW[(w, a, b)]`, `1`: `later`, `2`: `only_a`, `3`: `nv` (only if `a < b`). -/
def pwVar (L : Lay) (w a b i : Nat) : Nat := pwBase L + w * pwPerW L.n + pwOff L.n a b + i

def yBase (L : Lay) : Nat := pwBase L + L.n * pwPerW L.n

/-- `Y[t][i]`. -/
def yVar (L : Lay) (t i : Nat) : Nat := yBase L + t * L.NP + i

/-- `Pf[t][i]` (all `k·NP` `Y`s are allocated before the first `Pf`). -/
def pfVar (L : Lay) (k t i : Nat) : Nat := yBase L + k * L.NP + t * L.NP + i

/-- `e.n` after `build(n, k)`. -/
def numVars (L : Lay) (k : Nat) : Nat := yBase L + 2 * k * L.NP - 1

/-! ## Literals -/

def pos (v : Nat) : Int := (v : Int)
def neg (v : Nat) : Int := -((v : Int))

/-! ## Clauses, in Python program order -/

/-- ```
# initial state: identity matching, visited = diagonal
for m in range(n):
    for w in range(n):
        e.add(M[0][m][w] if m == w else -M[0][m][w])
        e.add(V[0][m][w] if m == w else -V[0][m][w])
``` -/
def initClauses (L : Lay) : List (List Int) :=
  (List.range L.n).flatMap fun m =>
    (List.range L.n).flatMap fun w =>
      [[if m = w then pos (mVar L 0 m w) else neg (mVar L 0 m w)],
       [if m = w then pos (vVar L 0 m w) else neg (vVar L 0 m w)]]

/-- ```
# one-hot rows and injective columns for every frame's matching
for t in range(F + 1):
    for m in range(n):
        e.add(*[M[t][m][w] for w in range(n)])
        for w1 in range(n):
            for w2 in range(w1 + 1, n):
                e.add(-M[t][m][w1], -M[t][m][w2])
    for w in range(n):
        for m1 in range(n):
            for m2 in range(m1 + 1, n):
                e.add(-M[t][m1][w], -M[t][m2][w])
``` -/
def matchingClauses (L : Lay) : List (List Int) :=
  (List.range (L.F + 1)).flatMap fun t =>
    ((List.range L.n).flatMap fun m =>
      ((List.range L.n).map fun w => pos (mVar L t m w)) ::
      ((List.range L.n).flatMap fun w1 =>
        (List.range L.n).filterMap fun w2 =>
          if w1 < w2 then some [neg (mVar L t m w1), neg (mVar L t m w2)] else none)) ++
    ((List.range L.n).flatMap fun w =>
      (List.range L.n).flatMap fun m1 =>
        (List.range L.n).filterMap fun m2 =>
          if m1 < m2 then some [neg (mVar L t m1 w), neg (mVar L t m2 w)] else none)

/-- ```
# step choice one-hot; stop absorbs
for t in range(F):
    e.add(*S[t])
    for a in range(NS + 1):
        for b in range(a + 1, NS + 1):
            e.add(-S[t][a], -S[t][b])
    if t + 1 < F:
        e.add(-S[t][0], S[t + 1][0])
``` -/
def stepClauses (L : Lay) : List (List Int) :=
  (List.range L.F).flatMap fun t =>
    ((List.range (L.NS + 1)).map fun j => pos (sVar L t j)) ::
    ((List.range (L.NS + 1)).flatMap fun a =>
      (List.range (L.NS + 1)).filterMap fun b =>
        if a < b then some [neg (sVar L t a), neg (sVar L t b)] else none) ++
    (if t + 1 < L.F then [[neg (sVar L t 0), pos (sVar L (t + 1) 0)]] else [])

/-- The transition clauses of one shape `sh = SH[j-1]` at frame `t`:
```
kk = len(sh)
moved = set(sh)
for i in range(kk):
    a, b = sh[i], sh[(i + 1) % kk]       # a takes b's wife
    for w in range(n):
        e.add(-S[t][j], -M[t][b][w], M[t + 1][a][w])
for m in range(n):
    if m in moved:
        continue
    for w in range(n):
        e.add(-S[t][j], -M[t][m][w], M[t + 1][m][w])
``` -/
def shapeClauses (L : Lay) (t j : Nat) (sh : List Nat) : List (List Int) :=
  let kk := sh.length
  ((List.range kk).flatMap fun i =>
    let a := sh.getD i 0
    let b := sh.getD ((i + 1) % kk) 0
    (List.range L.n).map fun w =>
      [neg (sVar L t j), neg (mVar L t b w), pos (mVar L (t + 1) a w)]) ++
  ((List.range L.n).flatMap fun m =>
    if sh.contains m then [] else
    (List.range L.n).map fun w =>
      [neg (sVar L t j), neg (mVar L t m w), pos (mVar L (t + 1) m w)])

/-- ```
# transitions
for t in range(F):
    # stop: frame copied
    for m in range(n):
        for w in range(n):
            e.add(-S[t][0], -M[t][m][w], M[t + 1][m][w])
    for j, sh in enumerate(SH, start=1):
        ... shapeClauses ...
    # no-revisit: a newly acquired partner must be fresh
    for m in range(n):
        for w in range(n):
            e.add(-M[t + 1][m][w], M[t][m][w], -V[t][m][w])
    # visited update: V_{t+1} <-> V_t \/ M_{t+1}
    for m in range(n):
        for w in range(n):
            e.add(-V[t][m][w], V[t + 1][m][w])
            e.add(-M[t + 1][m][w], V[t + 1][m][w])
            e.add(-V[t + 1][m][w], V[t][m][w], M[t + 1][m][w])
``` -/
def transitionClauses (L : Lay) (SH : List (List Nat)) : List (List Int) :=
  (List.range L.F).flatMap fun t =>
    ((List.range L.n).flatMap fun m =>
      (List.range L.n).map fun w =>
        [neg (sVar L t 0), neg (mVar L t m w), pos (mVar L (t + 1) m w)]) ++
    ((List.range SH.length).flatMap fun j' =>
      shapeClauses L t (j' + 1) (SH.getD j' [])) ++
    ((List.range L.n).flatMap fun m =>
      (List.range L.n).map fun w =>
        [neg (mVar L (t + 1) m w), pos (mVar L t m w), neg (vVar L t m w)]) ++
    ((List.range L.n).flatMap fun m =>
      (List.range L.n).flatMap fun w =>
        [[neg (vVar L t m w), pos (vVar L (t + 1) m w)],
         [neg (mVar L (t + 1) m w), pos (vVar L (t + 1) m w)],
         [neg (vVar L (t + 1) m w), pos (vVar L t m w), pos (mVar L (t + 1) m w)]])

/-- ```
# first-visit-order auxiliaries: C[m][a][b][t] <-> V_t[m][a] /\ ~V_t[m][b]
# before(m,a,b) = OR_t C
for m in range(n):
    for a in range(n):
        for b in range(n):
            if a == b: continue
            cs = []
            for t in range(F + 1):
                c = e.new()
                e.add(-c, V[t][m][a])
                e.add(-c, -V[t][m][b])
                e.add(c, -V[t][m][a], V[t][m][b])
                cs.append(c)
            bv = e.new()
            for c in cs:
                e.add(-c, bv)
            e.add(-bv, *cs)
``` -/
def beforeClauses (L : Lay) : List (List Int) :=
  (List.range L.n).flatMap fun m =>
    (List.range L.n).flatMap fun a =>
      (List.range L.n).flatMap fun b =>
        if a = b then [] else
        let cs := (List.range (L.F + 1)).map fun t => cVar L m a b t
        let bv := beforeVar L m a b
        ((List.range (L.F + 1)).flatMap fun t =>
          let c := cVar L m a b t
          [[neg c, pos (vVar L t m a)],
           [neg c, neg (vVar L t m b)],
           [pos c, neg (vVar L t m a), pos (vVar L t m b)]]) ++
        (cs.map fun c => [neg c, pos bv]) ++
        [neg bv :: cs.map pos]

/-- ```
# neither[m][{a,b}] <-> ~V_F[m][a] /\ ~V_F[m][b]
for m in range(n):
    for a in range(n):
        for b in range(a + 1, n):
            nv = e.new()
            e.add(-nv, -V[F][m][a])
            e.add(-nv, -V[F][m][b])
            e.add(nv, V[F][m][a], V[F][m][b])
``` -/
def neitherClauses (L : Lay) : List (List Int) :=
  (List.range L.n).flatMap fun m =>
    (List.range L.n).flatMap fun a =>
      (List.range L.n).flatMap fun b =>
        if a < b then
          let nv := neitherVar L m a b
          [[neg nv, neg (vVar L L.F m a)],
           [neg nv, neg (vVar L L.F m b)],
           [pos nv, pos (vVar L L.F m a), pos (vVar L L.F m b)]]
        else []

/-- ```
# men's read-off preference: PM[m][a][b] <-> before(m,a,b) \/ (neither /\ a<b)
for m in range(n):
    for a in range(n):
        for b in range(n):
            if a == b: continue
            p = e.new()
            bv = before[(m, a, b)]
            if a < b:
                nv = neither[(m, a, b)]
                e.add(-bv, p)
                e.add(-nv, p)
                e.add(-p, bv, nv)
            else:
                e.add(-bv, p)
                e.add(-p, bv)
``` -/
def pmClauses (L : Lay) : List (List Int) :=
  (List.range L.n).flatMap fun m =>
    (List.range L.n).flatMap fun a =>
      (List.range L.n).flatMap fun b =>
        if a = b then [] else
        let p := pmVar L m a b
        let bv := beforeVar L m a b
        if a < b then
          let nv := neitherVar L m a b
          [[neg bv, pos p], [neg nv, pos p], [neg p, pos bv, pos nv]]
        else
          [[neg bv, pos p], [neg p, pos bv]]

/-- ```
# women's read-off preference ... VW_t[w][m] := V[t][m][w].
for w in range(n):
    for a in range(n):
        for b in range(n):
            if a == b: continue
            cs = []
            for t in range(F + 1):
                c = e.new()
                e.add(-c, V[t][a][w])
                e.add(-c, -V[t][b][w])
                e.add(c, -V[t][a][w], V[t][b][w])
                cs.append(c)
            bv = e.new()
            for c in cs:
                e.add(-c, bv)
            e.add(-bv, *cs)
``` -/
def beforeWClauses (L : Lay) : List (List Int) :=
  (List.range L.n).flatMap fun w =>
    (List.range L.n).flatMap fun a =>
      (List.range L.n).flatMap fun b =>
        if a = b then [] else
        let cs := (List.range (L.F + 1)).map fun t => cWVar L w a b t
        let bv := beforeWVar L w a b
        ((List.range (L.F + 1)).flatMap fun t =>
          let c := cWVar L w a b t
          [[neg c, pos (vVar L t a w)],
           [neg c, neg (vVar L t b w)],
           [pos c, neg (vVar L t a w), pos (vVar L t b w)]]) ++
        (cs.map fun c => [neg c, pos bv]) ++
        [neg bv :: cs.map pos]

/-- ```
for w in range(n):
    for a in range(n):
        for b in range(n):
            if a == b: continue
            p = e.new()
            later = e.new()                     # b before a, a visited
            e.add(-later, beforeW[(w, b, a)])
            e.add(-later, V[F][a][w])
            e.add(later, -beforeW[(w, b, a)], -V[F][a][w])
            only_a = e.new()                    # a visited, b never
            e.add(-only_a, V[F][a][w])
            e.add(-only_a, -V[F][b][w])
            e.add(only_a, -V[F][a][w], V[F][b][w])
            terms = [later, only_a]
            if a < b:
                nv = e.new()
                e.add(-nv, -V[F][a][w])
                e.add(-nv, -V[F][b][w])
                e.add(nv, V[F][a][w], V[F][b][w])
                terms.append(nv)
            for tv in terms:
                e.add(-tv, p)
            e.add(-p, *terms)
``` -/
def pwClauses (L : Lay) : List (List Int) :=
  (List.range L.n).flatMap fun w =>
    (List.range L.n).flatMap fun a =>
      (List.range L.n).flatMap fun b =>
        if a = b then [] else
        let p := pwVar L w a b 0
        let later := pwVar L w a b 1
        let onlyA := pwVar L w a b 2
        let nv := pwVar L w a b 3
        let bwba := beforeWVar L w b a
        let vfa := vVar L L.F a w
        let vfb := vVar L L.F b w
        let terms := if a < b then [later, onlyA, nv] else [later, onlyA]
        [[neg later, pos bwba], [neg later, pos vfa], [pos later, neg bwba, neg vfa]] ++
        [[neg onlyA, pos vfa], [neg onlyA, neg vfb], [pos onlyA, neg vfa, pos vfb]] ++
        (if a < b then
          [[neg nv, neg vfa], [neg nv, neg vfb], [pos nv, pos vfa, pos vfb]]
         else []) ++
        (terms.map fun tv => [neg tv, pos p]) ++
        [neg p :: terms.map pos]

/-- ```
for t in range(k):
    e.add(*Y[t])
    for i in range(NP):
        e.add(-Y[t][i], Pf[t][i])
        if i > 0:
            e.add(-Pf[t][i - 1], Pf[t][i])
            e.add(-Pf[t][i], Pf[t][i - 1], Y[t][i])
        else:
            e.add(-Pf[t][0], Y[t][0])
``` -/
def selectorClauses (L : Lay) (k : Nat) : List (List Int) :=
  (List.range k).flatMap fun t =>
    ((List.range L.NP).map fun i => pos (yVar L t i)) ::
    ((List.range L.NP).flatMap fun i =>
      [neg (yVar L t i), pos (pfVar L k t i)] ::
      (if i > 0 then
        [[neg (pfVar L k t (i - 1)), pos (pfVar L k t i)],
         [neg (pfVar L k t i), pos (pfVar L k t (i - 1)), pos (yVar L t i)]]
       else
        [[neg (pfVar L k t 0), pos (yVar L t 0)]]))

/-- ```
for t in range(k - 1):
    # slot t+1's index j requires slot t's index <= j-1
    e.add(-Y[t + 1][0])
    for j in range(1, NP):
        e.add(-Y[t + 1][j], Pf[t][j - 1])
``` -/
def ladderClauses (L : Lay) (k : Nat) : List (List Int) :=
  (List.range (k - 1)).flatMap fun t =>
    [neg (yVar L (t + 1) 0)] ::
    ((List.range (L.NP - 1)).map fun j' =>
      let j := j' + 1
      [neg (yVar L (t + 1) j), pos (pfVar L k t (j - 1))])

/-- `inv[mu[m]] = m`, i.e. `inv[w]` is the position of `w` in `mu`. -/
def invOf (mu : List Nat) (w : Nat) : Nat := mu.idxOf w

/-- ```
for t in range(k):
    for i, mu in enumerate(P):
        inv = [0] * n
        for m in range(n):
            inv[mu[m]] = m
        for m in range(n):
            for w in range(n):
                if w == mu[m]: continue
                e.add(-Y[t][i], -PM[(m, w, mu[m])], -PW[(w, m, inv[w])])
``` -/
def blockClauses (L : Lay) (k : Nat) (P : List (List Nat)) : List (List Int) :=
  (List.range k).flatMap fun t =>
    (List.range P.length).flatMap fun i =>
      let mu := P.getD i []
      (List.range L.n).flatMap fun m =>
        (List.range L.n).filterMap fun w =>
          if w = mu.getD m 0 then none
          else some [neg (yVar L t i),
                     neg (pmVar L m w (mu.getD m 0)),
                     neg (pwVar L w m (invOf mu w) 0)]

/-! ## The formulas -/

/-- `sched_sat.build(n, k)`: the clause list, in program order. -/
def schedCNFn (n k : Nat) : List (List Int) :=
  let L := layout n
  let SH := cyclicShapes n
  let P := permsN n
  initClauses L ++ matchingClauses L ++ stepClauses L ++ transitionClauses L SH ++
  beforeClauses L ++ neitherClauses L ++ pmClauses L ++ beforeWClauses L ++ pwClauses L ++
  selectorClauses L k ++ ladderClauses L k ++ blockClauses L k P

/-- `e.n` after `build(n, k)`. -/
def numVarsn (n k : Nat) : Nat := numVars (layout n) k

/-- `--fix-prefix=sh0;sh1;...`: unit clause `S[t][SH.index(sh_t) + 1]` for
each prefix step `t` (in order). -/
def prefixUnits (n : Nat) (pre : List (List Nat)) : List (List Int) :=
  let L := layout n
  let SH := cyclicShapes n
  (List.range pre.length).map fun t =>
    [pos (sVar L t (SH.idxOf (pre.getD t []) + 1))]

/-- `build(n, k)` followed by `--fix-prefix=`. -/
def cubeCNFn (n k : Nat) (pre : List (List Nat)) : List (List Int) :=
  schedCNFn n k ++ prefixUnits n pre

/-- Order 6: `sched_sat.build(6, k)`. -/
def schedCNF (k : Nat) : List (List Int) := schedCNFn 6 k

/-- Order 6 cube: `sched_sat.build(6, k)` plus `--fix-prefix=`. -/
def cubeCNF (k : Nat) (pre : List (List Nat)) : List (List Int) := cubeCNFn 6 k pre

/-- The campaign formula: "some legal order-6 schedule has sc(R(S)) ≥ 49". -/
def schedCNF49 : List (List Int) := schedCNF 49

def numVars6 (k : Nat) : Nat := numVarsn 6 k

/-- `Satisfiable` is `SmpF5.Encoding.Satisfiable` (evalCNF over `Nat → Bool`). -/
def SchedSat49 : Prop := Satisfiable schedCNF49

end SchedCNF6
