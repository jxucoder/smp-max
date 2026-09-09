import SmpMax.Six.ScheduleEncoding
import SmpMax.Six.Schedule
import SmpMax.Six.CyclicShapes

/-!
# Campaign cubes (order 6), mirroring `tools/campaign/cube_campaign.py`

A cube is a prefix of min-first cyclic shapes plus a `stopped` flag
(`"0,1;2,3"`, `"0,1;stop"`, `"stop"`).  `canonicalCubes2` is the driver's
`root_cubes(2)` and `extendCanon` its `split_children`, both under the
first-appearance rule (a) and the legality checks of `apply_step`:
per-man cap 5 moves (trajectory length ≤ 6), no revisit on either side,
30-move budget.  The definitions are computable so that `export_cubes6`
can print the id lists and they can be compared with the driver's
(FAITHFULNESS_PLAN.md §3.5, §5.3, §11.1).
-/

namespace Cubes6

open SchedCNF6

structure Cube where
  steps   : List (List Nat)
  stopped : Bool
deriving Repr, DecidableEq

/-! ## First-appearance canonicity (rule (a)), plan §3.3 -/

/-- Order of first occurrence. -/
def firstOcc : List Nat → List Nat :=
  List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

/-- Number of distinct men in the steps before `t` (`len(used)`). -/
def usedBefore (S : List (List Nat)) (t : Nat) : Nat :=
  (firstOcc (S.take t).flatten).length

/-- Men of step `t` not seen in earlier steps (`newmen`). -/
def newMen (S : List (List Nat)) (t : Nat) : List Nat :=
  (S.getD t []).filter (fun m => decide (m ∉ (S.take t).flatten))

/-- `sorted(newmen) == list(range(len(used), len(used) + len(newmen)))`. -/
def canonAtB (S : List (List Nat)) (t : Nat) : Bool :=
  decide (((List.range 6).filter (fun x => decide (x ∈ newMen S t)))
          = List.range' (usedBefore S t) (newMen S t).length)

/-! ## Prefix legality, plan §5.3 (must equal `apply_step`) -/

def WFStepB (st : List Nat) : Bool :=
  decide (2 ≤ st.length) && decide st.Nodup && st.all (fun m => decide (m < 6))

/-- (i) budget ≤ 30, (iii) per-man cap (≤ 5 moves ⇔ trajectory length ≤ 6),
(iv) no man revisits a woman, (v) no woman revisits a man. -/
def legalPrefixB (S : List (List Nat)) : Bool :=
  S.all WFStepB &&
  decide ((S.map List.length).sum ≤ 30) &&
  (List.range 6).all (fun m => decide (strajM S m).Nodup && decide ((strajM S m).length ≤ 6)) &&
  (List.range 6).all (fun w => decide (strajW S w).Nodup)

def canonNextB (L : List (List Nat)) (sh : List Nat) : Bool :=
  canonAtB (L ++ [sh]) L.length && legalPrefixB (L ++ [sh])

/-! ## The cube lists, plan §3.5 -/

/-- `split_children(prefix, closed=False)`: the stop child, then the
rule-(a) canonical one-step extensions in `cyclicShapes 6` order. -/
def extendCanon (c : Cube) : List Cube :=
  ⟨c.steps, true⟩ ::
  ((cyclicShapes 6).filter (canonNextB c.steps)).map (fun sh => ⟨c.steps ++ [sh], false⟩)

/-- `root_cubes(2)`: `stop`; `s1;stop` for each canonical `s1`; then the
open depth-2 prefixes `s1;s2`. -/
def canonicalCubes2 : List Cube :=
  let l1 := (cyclicShapes 6).filter (canonNextB [])
  ⟨[], true⟩ :: (l1.map fun s1 => ⟨[s1], true⟩) ++
  (l1.flatMap fun s1 =>
    ((cyclicShapes 6).filter (canonNextB [s1])).map fun s2 => ⟨[s1, s2], false⟩)

/-- Adaptive splitting: replace every cube selected by `split` by its
children (`cube_campaign.py` enqueues `split_children` of a timed-out
open cube below `--max-depth`). -/
def refineCubes (cs : List Cube) (split : Cube → Bool) : List Cube :=
  cs.flatMap (fun c =>
    if split c && !c.stopped && decide (c.steps.length < 15) then extendCanon c else [c])

/-! ## Ids, exactly `cube_campaign.cube_id` -/

def stepId (st : List Nat) : String := String.intercalate "," (st.map toString)

def cubeId (c : Cube) : String :=
  let parts := c.steps.map stepId
  let parts := if c.stopped then parts ++ ["stop"] else parts
  if parts.isEmpty then "stop" else String.intercalate ";" parts

/-- The CNF of a cube: base formula + one unit per fixed step, plus the
`S[len][0]` unit for a stopped cube (plan §3.5; `cube_units`). -/
def stopUnits (n : Nat) (pre : List (List Nat)) (stopped : Bool) : List (List Int) :=
  if stopped then [[pos (sVar (layout n) pre.length 0)]] else []

def cubeCNFc (n k : Nat) (c : Cube) : List (List Int) :=
  schedCNFn n k ++ prefixUnits n c.steps ++ stopUnits n c.steps c.stopped

/-! ## Side conditions and the fit relation (plan §3.5) -/

/-- Well-formedness the formula needs: every prefix shape is in the shape
alphabet, at most 15 steps, and a stopped cube stops strictly before frame
15 (`sVar L 15 0` aliases a `C` variable, plan §0). -/
def CubeWF (c : Cube) : Prop :=
  c.steps.length ≤ 15 ∧ (c.stopped = true → c.steps.length < 15) ∧
  ∀ sh ∈ c.steps, sh ∈ cyclicShapes 6

/-- `c` fits the schedule `S`: the cube's steps are the min-first forms of
the first `c.steps.length` steps of `S`, and a stopped cube fits only a
schedule of exactly that length. -/
def Fits (c : Cube) (S : List (List Nat)) : Prop :=
  c.steps = (S.take c.steps.length).map minFirst ∧
  c.steps.length ≤ S.length ∧
  (c.stopped = true → S.length = c.steps.length)

/-- The formula of a cube at target `k`: the file the campaign solved. -/
def cubeFormula (k : Nat) (c : Cube) : List (List Int) := cubeCNFc 6 k c

end Cubes6
