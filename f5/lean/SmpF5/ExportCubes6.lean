import SmpF5.SplitList6

/-!
`export_cubes6 OUT`                 prints the ids of `Cubes6.canonicalCubes2`, one per line
`export_cubes6 OUT --parents=FILE`  for each cube id in FILE prints
                                    `<parent>\t<child>` for every child of `extendCanon`
`export_cubes6 OUT --final`         prints the ids of `Cubes6.finalCubes` (the certified leaves)
`export_cubes6 OUT --units=FILE`    for each cube id in FILE prints `<id>\t<unit clauses>`,
                                    the unit clauses of `cubeCNFc` (`prefixUnits` then
                                    `stopUnits`), DIMACS lines joined by `|`
-/

open Cubes6

def parseNat (s : String) : Nat := s.trimAscii.toString.toNat!

def parseCubeId (s : String) : Cube :=
  let parts := (s.trimAscii.toString.splitOn ";").filter (fun p => !p.isEmpty)
  let stopped := parts.getLast? == some "stop"
  let parts := if stopped then parts.dropLast else parts
  let steps := parts.filter (· ≠ "stop") |>.map fun g => (g.splitOn ",").map parseNat
  ⟨steps, stopped⟩

def clauseLine (c : List Int) : String :=
  String.intercalate " " (c.map toString) ++ " 0"

/-- The unit clauses of `cubeCNFc 6 k c` (independent of `k`). -/
def unitsOf (c : Cube) : List (List Int) :=
  SchedCNF6.prefixUnits 6 c.steps ++ stopUnits 6 c.steps c.stopped

def main (args : List String) : IO UInt32 := do
  let mut out : Option String := none
  let mut parents : Option String := none
  let mut units : Option String := none
  let mut final := false
  for a in args do
    if a.startsWith "--parents=" then parents := some (a.drop 10).toString
    else if a.startsWith "--units=" then units := some (a.drop 8).toString
    else if a == "--final" then final := true
    else out := some a
  let some path := out | do
    IO.eprintln "usage: export_cubes6 OUT [--parents=FILE | --final | --units=FILE]"
    return 1
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  match parents, units with
  | some pf, _ =>
    let lines ← IO.FS.lines pf
    let mut n := 0
    for ln in lines do
      if ln.trimAscii.isEmpty then continue
      let c := parseCubeId ln
      for k in extendCanon c do
        h.putStrLn s!"{cubeId c}\t{cubeId k}"
        n := n + 1
    IO.println s!"{n} children of {lines.size} parents -> {path}"
  | none, some uf =>
    let lines ← IO.FS.lines uf
    let mut n := 0
    for ln in lines do
      if ln.trimAscii.isEmpty then continue
      let c := parseCubeId ln
      h.putStrLn s!"{cubeId c}\t{String.intercalate "|" ((unitsOf c).map clauseLine)}"
      n := n + 1
    IO.println s!"units of {n} cubes -> {path}"
  | none, none =>
    if final then
      let cs := finalCubes
      for c in cs do
        h.putStrLn (cubeId c)
      IO.println s!"{cs.length} final cubes -> {path}"
    else
      let cs := canonicalCubes2
      for c in cs do
        h.putStrLn (cubeId c)
      IO.println s!"{cs.length} root cubes -> {path}"
  h.flush
  return 0
