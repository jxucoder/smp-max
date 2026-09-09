import SmpMax.Five.Encoding

def clauseLine (c : List Int) : String :=
  String.intercalate " " (c.map toString) ++ " 0"

def dimacs (F : List (List Int)) : String :=
  s!"p cnf {numVars} {F.length}\n" ++
  String.intercalate "\n" (F.map clauseLine) ++ "\n"

def pad3 (i : Nat) : String :=
  if i < 10 then s!"00{i}" else if i < 100 then s!"0{i}" else s!"{i}"

def main : IO Unit := do
  IO.FS.writeFile "perms120.txt" (String.intercalate "\n"
    (perms120.map fun p => String.intercalate " " (p.map toString)) ++ "\n")
  for i in List.range 120 do
    let row := perms120.getD i []
    IO.FS.writeFile s!"cubeL{pad3 i}.cnf" (dimacs (cubeCNF row))
    IO.FS.writeFile s!"cubeL16_{pad3 i}.cnf" (dimacs (cubeCNF16 row))
  IO.println s!"wrote 120+120 files, {(cubeCNF (perms120.getD 0 [])).length} / {(cubeCNF16 (perms120.getD 0 [])).length} clauses"
