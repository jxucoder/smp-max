import SmpF5.Cubes6

/-!
`export_cubes6 OUT`            prints the ids of `Cubes6.canonicalCubes2`, one per line
`export_cubes6 OUT --parents=FILE`  for each cube id in FILE prints
                               `<parent>\t<child>` for every child of `extendCanon`
-/

open Cubes6

def parseNat (s : String) : Nat := s.trimAscii.toString.toNat!

def parseCubeId (s : String) : Cube :=
  let parts := (s.trimAscii.toString.splitOn ";").filter (fun p => !p.isEmpty)
  let stopped := parts.getLast? == some "stop"
  let parts := if stopped then parts.dropLast else parts
  let steps := parts.filter (· ≠ "stop") |>.map fun g => (g.splitOn ",").map parseNat
  ⟨steps, stopped⟩

def main (args : List String) : IO UInt32 := do
  let mut out : Option String := none
  let mut parents : Option String := none
  for a in args do
    if a.startsWith "--parents=" then parents := some (a.drop 10).toString
    else out := some a
  let some path := out | do
    IO.eprintln "usage: export_cubes6 OUT [--parents=FILE]"
    return 1
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  match parents with
  | none =>
    let cs := canonicalCubes2
    for c in cs do
      h.putStrLn (cubeId c)
    IO.println s!"{cs.length} root cubes -> {path}"
  | some pf =>
    let lines ← IO.FS.lines pf
    let mut n := 0
    for ln in lines do
      if ln.trimAscii.isEmpty then continue
      let c := parseCubeId ln
      for k in extendCanon c do
        h.putStrLn s!"{cubeId c}\t{cubeId k}"
        n := n + 1
    IO.println s!"{n} children of {lines.size} parents -> {path}"
  h.flush
  return 0
