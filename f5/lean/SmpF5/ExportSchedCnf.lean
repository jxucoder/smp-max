import SmpF5.SchedCNF6

/-!
`export_sched_cnf OUT [--n=N] [--k=K] [--prefix=a,b;c,d,e]`

Prints `SchedCNF6.schedCNFn N K` (default N=6, K=49, i.e. `schedCNF49`)
as DIMACS to OUT, or the cube `cubeCNFn N K prefix` when `--prefix=` is
given (the same syntax as `sched_sat.py --fix-prefix=`).  Header is
`p cnf <numVars> <numClauses>` exactly as `Enc.write`.
-/

open SchedCNF6

def clauseLine (c : List Int) : String :=
  String.intercalate " " (c.map toString) ++ " 0"

def parseNat (s : String) : Nat := s.trimAscii.toString.toNat!

def parsePrefix (s : String) : List (List Nat) :=
  if s.isEmpty then [] else
  (s.splitOn ";").map fun g => (g.splitOn ",").map parseNat

def main (args : List String) : IO UInt32 := do
  let mut out : Option String := none
  let mut n := 6
  let mut k := 49
  let mut pre : List (List Nat) := []
  for a in args do
    if a.startsWith "--n=" then n := parseNat (a.drop 4).toString
    else if a.startsWith "--k=" then k := parseNat (a.drop 4).toString
    else if a.startsWith "--prefix=" then pre := parsePrefix (a.drop 9).toString
    else out := some a
  let some path := out | do
    IO.eprintln "usage: export_sched_cnf OUT [--n=N] [--k=K] [--prefix=a,b;c,d]"
    return 1
  let F := if pre.isEmpty then schedCNFn n k else cubeCNFn n k pre
  let nv := numVarsn n k
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  h.putStrLn s!"p cnf {nv} {F.length}"
  for c in F do
    h.putStrLn (clauseLine c)
  h.flush
  IO.println s!"n={n} k={k}: {nv} vars, {F.length} clauses -> {path}"
  return 0
