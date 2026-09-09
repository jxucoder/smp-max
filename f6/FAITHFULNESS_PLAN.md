# Faithfulness plan: Lean proof that the order-6 schedule CNF is faithful

Status: **COMPLETE (2026-09-08, evening)** — `f6_eq_48_of_unsat` is proved;
see the last progress-log entry. Below is revision 2 of the plan
(2026-09-02, after an independent critique of revision 1), kept as the
record of what was planned; the progress log records what was built. Target file set lives next to the existing
order-6 development in `f5/lean/SmpF5/SmpF5/` (same `lakefile`, Mathlib
v4.33.1); the f(5) files `Encoding.lean` / `Faithfulness.lean` /
`Bridge.lean` / `ExportCnf.lean` are the pattern.

**What changed in revision 2.** Revision 1 proposed a fresh closed-form
variable layout (`Encoding6.lean`, `shapes6` in sublist order, `perms720 :=
idRow6.permutations`, a new printer). That formula would *not* have been
certificate-compatible with the formula the campaign actually solves. The
Lean transcription of `sched_sat.py` already exists —
`SmpF5/SchedCNF6.lean` (584 lines) with the exporter `ExportSchedCnf.lean`
(44 lines) — and its DIMACS output is **byte-identical** to the Python
writer (full n=6, k=49 formula: sha256 `28421fb6…`, 84,882 vars /
2,709,212 clauses; the `(0,1);(2,3)` cube; the n=5, k=17 pilot). The
faithfulness proof is therefore built *on top of `SchedCNF6`'s definitions
exactly as they are*: Python allocation order for variables, `cyclicShapes
6` (409 shapes, Python order) for steps, `permsN 6` (720 matchings,
`itertools.permutations` order) for the selector, and `prefixUnits` for
cubes. Sections 4–8 are rewritten accordingly; §0/§11 record the rule-(b)
facts precisely; the stopped-cube variable-range bug is fixed (§3.5);
`minFirst` invariance lemmas are added and used where revision 1 quietly
discharged legality on un-rotated steps (§4.2, L3.17).

## Progress log

- **2026-09-08 (step 0, 0', 9-def, 12; §11.1 resolved).** `SmpF5/Cubes6.lean`
  (definitions only: `Cube`, `firstOcc`/`usedBefore`/`newMen`/`canonAtB`,
  `WFStepB`/`legalPrefixB`/`canonNextB`, `extendCanon`, `canonicalCubes2`,
  `refineCubes`, `cubeId`, `stopUnits`/`cubeCNFc`) and the printer
  `ExportCubes6.lean` (`export_cubes6`). **Cube-list identity holds by
  construction and was checked:** `canonicalCubes2` prints the driver's
  `root_cubes(2)` ids **byte-identical, same order (25,493)**, and
  `extendCanon` prints `split_children` of every journaled split parent
  of the campaign **byte-identical (2,756 parents, 295,999 children)**.
  `export_sched_cnf --stop` (via `cubeCNFc`) prints the closed cubes:
  sha256 of `stop`, `0,1;stop`, `0,1,2;stop` and of the open
  `0,5,4,2,1,3;0,2,5,1,3,4` all equal the journaled `cnf_sha256`
  (`3de5bab1…`, `bbb84011…`, `c5a479da…`, `f2ea077c…`). Risk 1 retired.
- **2026-09-08 (positive control, §8).** The dihedral 48-schedule in
  rule-(a) canonical form,
  `0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5` (15
  transpositions, full budget; `apply_step`-legal), pinned as a 15-unit
  `--prefix` (no `--stop`: a 15-step cube has no frame to stop in, cf. the
  `sVar L 15 0` alias): `export_sched_cnf --k=48` is **SAT** (cadical,
  < 1 s); the model decodes (`sched_sat.decode`) to exactly the pinned
  schedule with 48 distinct selected matchings, and `readoff_counts`
  recounts the read-off at 48. The same prefix at `--k=49` is UNSAT. So
  the formula is not vacuously unsatisfiable and the selector block does
  count what it should on the extremal instance.

- **2026-09-08 03:00 (files 1–6 of §8 done, zero sorries).** `Decode6.lean`
  (L4.1–L4.3: layout `⟨6,15,409,720⟩` by kernel evaluation, pair tables,
  twelve decode lemmas), `DestutterPrefix6.lean` (§5.1, restated around
  first-occurrence positions: `mem_destutter_ne_iff`,
  `idxOf_destutter_lt_iff`, `mem_take_iff_idxOf_lt`, `idxOf_reverse_lt_iff`,
  `idxOf_filter_range_lt`), `Shapes6.lean` (L4.5–L4.13, L4.15–L4.17:
  `rotateTo`/`minFirst`, `applyStep_rotate`, `Legal_map_minFirst`,
  `mem_combos`, `mem_permsOf`, `permsOf_nodup`,
  `minFirst_mem_cyclicShapes`, `permsN6_perm_permutations`), `Frames6.lean`
  (§4.4: `frame`/`colM`/`vis`/`stepIdx`/`befB`/`befWB`, `τV`, `tau6`,
  L4.19–L4.27, `evalLit_pos6/neg6`), `ReadoffSem6.lean` (**L5.13 `PM_sem`,
  L5.15 `PW_sem` proved**, via `befB_iff`/`befWB_iff`/`rowOrder_lt_iff`),
  `SchedLen6.lean` (L2.1–L2.6: `movesOf`, `strajM_length`, `moves_le_30`,
  `Legal_length_le_15`). `lake build` passes with all files imported.
  Remaining: Cubes6 proofs (L3.17–L3.21, L5.10–L5.12), RelabelSched6 +
  FirstApp6 (§3), Faithfulness6 (§6 families + §7 assembly), Bridge6.


- **2026-09-08 evening (files 7–12 and the assembly; COMPLETE).** Layer 0
  first: `CubeWF`, `Fits`, `cubeFormula` added to `Cubes6.lean`,
  `relabelSched` in `RelabelSched6.lean`, and `SplitList6.lean` generated
  from the journal (the 1,804 depth-2 and 952 depth-3 split ids;
  `finalCubes := refineCubes (refineCubes canonicalCubes2 isSplitDepth2)
  isSplitDepth3`, 318,736 leaves = the journal's `verified` ids;
  `export_cubes6 --final/--units`, all 321,492 `cnf_sha256` re-hashed from
  Lean — `campaign/lean_identity.txt`). Then nine files in parallel:
  `RelabelSched6` (L3.1–L3.7, L3.12–L3.16; 391 lines), `FirstApp6`
  (`partOrder`, `sigmaOf`, L3.8–L3.11, L4.14, L3.21; 502), `PrefixLegal6`
  (L5.10–L5.12; 193), `FamState6` (families 1–3; 209), `FamTrans6` (L5.9
  and family 4; 337), `FamGates6` (families 5–9; 363), `FamSelect6`
  (families 10–12, L4.18, `idxsOf`; 308), `Units6` (13–14; 110), `Lower6`
  (`dihedral6_count : stableCount6 dihedral6 = 48`; 77); then `Coverage6`
  (L3.17–L3.20, `fits_final`), `Faithfulness6` (`schedCNF_sat`,
  `cube_faithful6`, `exists_canonical_schedule`), `Bridge6`
  (`f6_upper_of_unsat`, `f6_eq_48_of_unsat`). Deviations from the plan:
  the twelve families live in four files; `block_sat` is `block_sat6`
  (name clash with f(5)); the count chain goes through
  `exists_canonical_schedule` and `f6_upper_of_unsat_of_coverage`. Final
  statement: `f6_eq_48_of_unsat : (∀ c ∈ finalCubes, ¬ Satisfiable
  (cubeFormula 49 c)) → (∀ I, WF6 I = true → stableCount6 I ≤ 48) ∧ ∃ I,
  WF6 I = true ∧ stableCount6 I = 48`; `#print axioms` = [propext,
  Classical.choice, Quot.sound]; `lake build` 893 jobs, no `sorry`.
  Faithfulness layer: 19 files, 4,761 lines, 333 theorems (+ 2,808 lines
  of data). Risks 2 and 3 (`firstApp_relabel`, `shapeClauses_sat`) closed
  without changing any definition.

## 0. Target theorem and what already exists

```lean
-- Cubes6.lean
structure Cube where
  steps   : List (List Nat)   -- the cube id's prefix: min-first shapes, each ∈ cyclicShapes 6
  stopped : Bool              -- "…;stop": pin S[steps.length][0]
deriving Repr, DecidableEq

def cubeFormula (k : Nat) (c : Cube) : List (List Int) :=
  Cubes6.cubeCNFc 6 k c    -- as realized in Cubes6.lean (c : Cube)
  -- = schedCNFn 6 k ++ prefixUnits 6 c.steps ++ stopUnits 6 c.steps c.stopped   (§4.1)

theorem campaign_faithful {I : Inst6} (hWF : WF6 I = true)
    (h49 : 49 ≤ stableCount6 I) :
    ∃ c ∈ canonicalCubes2, Satisfiable (cubeFormula 49 c)
```

`canonicalCubes2` = the campaign's `root_cubes(2)` (`cube_campaign.py`):
the cube `stop`, the 153 cubes `s1;stop`, and the 25,339 open depth-2
prefixes under first-appearance rule (a) with the legality filter of
`apply_step` (§3.5); 25,493 in total. `Satisfiable` is
`SmpF5.Encoding.Satisfiable` (∃ τ : Nat → Bool, evalCNF τ F = true), the
same predicate `SchedCNF6.SchedSat49` uses.

**The formula is fixed, not designed.** `SchedCNF6.schedCNFn 6 49` is the
clause list kissat / drat-trim / cake_lpr see, literal for literal. Every
certificate the campaign produces is valid *only* for this byte-identical
formula plus the cube's unit clauses; nothing in this plan may change a
clause, a variable id, a shape index or a matching index. The proof
adapts to the formula, never the other way round.

Already proved (zero sorries, standard axioms), reused verbatim:

| fact | file | used for |
|---|---|---|
| `validity_unconditional`, `manOpt_wrelabel6`, `stableCount6_wrelabel6`, `WF6_wrelabel6` | WRelabel6 | witness schedule (§1) |
| `Legal_chainSched`, `strajM_eq_traj`, `strajW_eq_wtraj`, `linkSteps`/`chainSched` | ChainSched6 | witness (§1), bridge at the relabeled schedule (§3.4) |
| `traj_mem_iff`, `traj_rank_pairwise`, `wtraj_rank_pairwise`, `wtraj_mem_iff`, `traj_length_le`, `total_moves_le_30` | Chain6 / ValidityBridge6 | bridge hypotheses (§3.4), frame bound alternative (§2) |
| `get2_readoffS_mrank/wrank`, `idxOf_append_mem/notMem`, `idxOf_lt_of_sorted`, `readoffS_*` | ValidityBridge6 | non-blocking family (§6.12), bridge (§3.4) |
| `relabel6`, `mapMu6`, `mapMu6_getD/idxOf/perm`, `isStable6_relabel6`, `stableCount6_relabel6`, `app_inj6`, `inv_app_app6`, `app_inv_app6`, `app_lt6` … | Sym6 / Symmetry | schedule relabel (§3) |
| `count_le_of_orderPreserving` | AbsBridge6 | bridge (§3.4) |
| `applyStep`, `applyStep_getD`, `applyStep_perm`, `schedMatchings` (= `scanl`), `schedMatchings_perm`, `strajM/W`, `Legal`, `rowOrderM/W`, `readoffS`, `WF6_readoffS`, `rowOrderM/W_perm`, `perm6_of_nodup_lt`, `step_succ_inj` | Sched6 | everything |
| `stepDecomp_spec`, `orbit_*` | Cycle6 | only indirectly (chainSched steps are single orbits) |
| `evalLit/evalClause/evalCNF/Satisfiable`, `idxOf_map`, `getD_map_nat`, `getD_map_range6` | Encoding / Symmetry / SixBridge | CNF semantics, list plumbing |
| `sms6 I = idRow6.permutations.filter (isStable6 I)`, `stableCount6` | SixBridge | count chain (§7) |
| **`SchedCNF6`: `Lay`/`layout`, `opIdx`, `upIdx`, `mVar`, `vVar`, `sBase`/`sVar`, `beforeBase`/`cVar`/`beforeVar`, `neitherBase`/`neitherVar`, `pmBase`/`pmVar`, `beforeWBase`/`cWVar`/`beforeWVar`, `pwBase`/`opairs`/`pwWidth`/`pwOff`/`pwPerW`/`pwVar`, `yBase`/`yVar`/`pfVar`, `numVars`, `pos`/`neg`, `combos`/`picks`/`permsAux`/`permsOf`/`cyclicShapes`/`permsN`, the 12 clause families, `schedCNFn`, `prefixUnits`, `cubeCNFn`, `schedCNF`, `cubeCNF`** | SchedCNF6 (exists) | the formula (§4, §6) |
| `export_sched_cnf` | ExportSchedCnf (exists) | the printer (§7, §9) |
| Mathlib: `List.map_destutter` (local-injectivity form), `destutter_sublist`, `destutter_cons'`, `destutter'_cons_pos/neg`, `mem_destutter'`, `nodup_permutations`, `mem_permutations`, `perm_ext_iff_of_nodup` | Mathlib.Data.List.* | trajectory equivariance, prefix lemmas, `permsN 6` vs `idRow6.permutations` |

Design facts that shape the plan (verified while reading):

* `chainSched J = linkSteps (theChain J)`; every step is one `orbit μ ν m0`
  with `m0` the least man of its orbit (`stepDecompAux` scans `idRow6` in
  order). So the witness steps are single cycles and **are already
  min-first before relabeling**. The σ-relabeled schedule (§3) is *not*
  min-first (`app σ` need not preserve the minimum), hence `minFirst`
  (§4.2) is still needed: the SAT one-hot `S[t][j]` ranges over the
  min-first shapes `cyclicShapes 6`.
* `Legal` has no explicit step-count bound; the frame bound 15 must be a
  theorem (§2).
* `readoffS` does not commute with `relabel6` (bottom completion). The plan
  never states `readoffS (σ·S) = relabel6 σ (readoffS S)`; the bridge is
  re-instantiated at the relabeled level (§3.4).
* `sched_sat.py` numbers variables by allocation order and `SchedCNF6`
  reproduces that order with explicit per-block offset functions
  (`mVar`, `vVar`, `sVar`, `cVar`, `beforeVar`, `neitherVar`, `pmVar`,
  `cWVar`, `beforeWVar`, `pwVar`, `yVar`, `pfVar`). The assignment is a
  `Nat → Bool` obtained by *decoding* an id back to its block (§4.1),
  exactly as f(5)'s `tau` divides by 10 and 120.
* `SchedCNF6.prefixUnits` uses `List.idxOf` on `cyclicShapes 6`: a shape
  not in the list gets index 409, and `sVar L t 410 = sVar L (t+1) 0`
  (the next frame's *stop* variable) — a silent alias. And
  `sVar L 15 0 = 1153 + 15·410 = 7303 = beforeBase L = cVar L 0 0 1 0`: a
  stop unit at step index 15 would pin a `C` auxiliary, not a step. Both
  are outside the campaign's use (all its shapes come from
  `cyclic_shapes(6)`; its deepest stop cube has depth ≤ 4) but the theorem
  must carry the hypotheses explicitly: `CubeWF` (§3.5) requires every
  prefix shape ∈ `cyclicShapes 6`, `steps.length ≤ 15`, and
  `stopped → steps.length < 15`.
* Rule (b) (backward commutation), precisely: `cube_calibrate.py` compares
  *tuples lexicographically* (`st < prev`); `gen_enum.c` compares *step
  indices* in its own size-first enumeration (all 2-cycles, then 3-cycles,
  …). Under rule (a), rule (b)-lex is **vacuous at depth 2**: a step
  disjoint from step 1 consists of fresh men, so its min-first tuple starts
  with a label > 0 = first element of step 1 and is never lex-smaller.
  Counted: rule (a) + legality = 25,339 = rule (a)+(b)-lex + legality
  (sets identical). Rule (b)-index is *not* vacuous at depth 2 (a 2-cycle
  on fresh men after a 3-cycle has a smaller size-first index), which is
  why `gen_enum.c`'s depth-3 count 1,818,512 differs from the rule-(a)-only
  1,833,929 and from a rule-(a)+(b)-lex count; all three prunings are
  sound (commuting disjoint adjacent steps preserves the read-off). The
  campaign and this proof use **rule (a) only**; no rule (b) lemma exists
  or is needed.

## 1. The witness schedule

No new schedule construction. Unfold `validity_unconditional`:

```
hne : sms6 I ≠ []                          (from 49 ≤ stableCount6 I)
J   := wrelabel6 (invMatch (manOpt I)) I    WF6 J, manOpt J = idRow6, sc J = sc I
S   := chainSched J                         Legal S (Legal_chainSched)
```

Its steps are single orbits (`linkSteps` concatenates `stepDecomp μ ν`,
whose members are `orbit μ ν m0`), each `WFStep`. We do not use
`validity_unconditional` as a black box because its inequality is about
`readoffS S`, whereas the CNF is about the *relabeled* `S'` (§3). Instead we
reuse its ingredients (`hWFJ`, `hneJ`, `hmo`) and prove the inequality at
`S'` directly (§3.4).

## 2. The frame bound (must be proved) — file `SchedLen6.lean`

The CNF has F = 15 frames (`(layout 6).F = 15`); the assignment (§4.4)
needs `S'.length ≤ 15`. Since `(relabelSched σ S).length = S.length`, it
suffices to bound `S`. The general route is taken because it is reusable
for any `Legal` schedule (prefixes, refined cubes, the campaign's
budget/cap checks in §5.3) and does not depend on the chain.

**L2.1** `applyStep_moves` — every listed man really moves.
```lean
theorem applyStep_moves {st mu : List Nat} (hst : WFStep st) (hmu : mu.Perm idRow6)
    {m : Nat} (hm : m ∈ st) : (applyStep st mu).getD m 0 ≠ mu.getD m 0
```
Proof: `applyStep_getD`, successor `st.getD ((idxOf m st + 1) % len)` is a
step member ≠ m (`step_succ_inj`/Nodup + length ≥ 2), then `perm6_getD_inj`.
~40 lines.

**L2.2** `length_destutter_ne_eq_changes`
```lean
def changes : List Nat → Nat
  | a :: b :: l => (if a ≠ b then 1 else 0) + changes (b :: l)
  | _ => 0
theorem length_destutter_ne {l : List Nat} (h : l ≠ []) :
    (l.destutter (· ≠ ·)).length = changes l + 1
```
Induction via `destutter'`. ~50 lines.

**L2.3** `changes_col_eq_count`
```lean
theorem changes_col_eq_count {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st)
    {m : Nat} (hm : m < 6) :
    changes ((schedMatchings S).map (fun mu => mu.getD m 0))
      = (S.filter (fun st => decide (m ∈ st))).length
```
Induction on `S` generalizing the start matching (a `scanl` variant), using
L2.1 and `applyStep_getD` (`m ∉ st` branch). ~60 lines.

**L2.4** `sum_lengths_double_count`
```lean
theorem sum_lengths_double_count {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    (S.map List.length).sum
      = ((List.range 6).map (fun m => (S.filter (fun st => decide (m ∈ st))).length)).sum
```
~50 lines.

**L2.5** `strajM_length_le_6` (from `Legal` Nodup + `strajM_all_lt6`). ~15 lines.
Also used for the campaign's per-man cap (§5.3).

**L2.6** `Legal_length_le_15`
```lean
theorem Legal_length_le_15 {S : List (List Nat)} (hL : Legal S) : S.length ≤ 15
```
`2 * S.length ≤ (S.map length).sum` (each ≥ 2) `= Σ_m count_m = Σ_m (|strajM S m| - 1) ≤ 6·5 = 30`.
The intermediate `moves_le_30 : Legal S → (S.map length).sum ≤ 30` is
stated separately (the campaign's budget check, §5.3). ~40 lines.

## 3. Canonical-cube coverage: schedule-level relabel

### 3.1 Definitions

```lean
def relabelSched (σ : List Nat) (S : List (List Nat)) : List (List Nat) :=
  S.map (fun st => st.map (app σ))
```
Men and women are relabeled by the *same* σ, matching `relabel6 σ` and
`mapMu6 σ mu = σ ∘ mu ∘ σ⁻¹`.

### 3.2 Equivariance and legality (file `RelabelSched6.lean`)

**L3.1** `mapMu6_idRow6 : σ.Perm idRow6 → mapMu6 σ idRow6 = idRow6` (~15).

**L3.2** `applyStep_relabel`
```lean
theorem applyStep_relabel {σ st mu : List Nat} (hp : σ.Perm idRow6)
    (hst : WFStep st) (hmu : mu.Perm idRow6) :
    applyStep (st.map (app σ)) (mapMu6 σ mu) = mapMu6 σ (applyStep st mu)
```
`perm6_ext`; pointwise at `m' = app σ m`: `idxOf (app σ m) (st.map (app σ)) = idxOf m st`
(`idxOf_map` with `app_inj6` restricted to `st`), `getD_map_nat`, `mapMu6_getD`,
`inv_app_app6`. ~70 lines.

**L3.3** `schedMatchings_relabel`
```lean
theorem schedMatchings_relabel {σ : List Nat} (hp : σ.Perm idRow6)
    {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    schedMatchings (relabelSched σ S) = (schedMatchings S).map (mapMu6 σ)
```
`scanl` induction generalizing the start. ~45 lines.

**L3.4** `strajM_relabel`, **L3.5** `strajW_relabel`
```lean
theorem strajM_relabel (hp) (hWF) {m : Nat} (hm : m < 6) :
    strajM (relabelSched σ S) (app σ m) = (strajM S m).map (app σ)
theorem strajW_relabel (hp) (hWF) {w : Nat} (hw : w < 6) :
    strajW (relabelSched σ S) (app σ w) = (strajW S w).map (app σ)
```
L3.3, `List.map_map`, `mapMu6_getD` resp. `mapMu6_idxOf`, then Mathlib
`List.map_destutter` with the local relation transfer
`a ≠ b ↔ app σ a ≠ app σ b` on the column (all < 6 by `schedMatchings_perm`).
~50 + ~45 lines.

**L3.6** `Legal_relabel`
```lean
theorem Legal_relabel {σ : List Nat} (hp : σ.Perm idRow6) {S : List (List Nat)}
    (hL : Legal S) : Legal (relabelSched σ S)
```
~60 lines.

**L3.7** `length_relabelSched : (relabelSched σ S).length = S.length` (simp).

### 3.3 First-appearance normalization (file `FirstApp6.lean`)

Rule (a) (`cube_campaign.apply_step`, `gen_enum.c`): at each step, the
*set* of men not seen in earlier steps must be exactly the next contiguous
block of labels `[used, used + k_new)`.

```lean
def firstOcc : List Nat → List Nat :=
  List.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []
def partOrder (S : List (List Nat)) : List Nat := firstOcc (S.flatten ++ idRow6)
def sigmaOf (S : List (List Nat)) : List Nat := invMatch (partOrder S)
-- app (sigmaOf S) m = idxOf m (partOrder S) : new label = position of first participation
def usedBefore (S : List (List Nat)) (t : Nat) : Nat := (firstOcc (S.take t).flatten).length
def newMen (S : List (List Nat)) (t : Nat) : List Nat :=
  (S.getD t []).filter (fun m => decide (m ∉ (S.take t).flatten))
def canonAtB (S : List (List Nat)) (t : Nat) : Bool :=
  decide (((List.range 6).filter (fun x => decide (x ∈ newMen S t)))
          = List.range' (usedBefore S t) (newMen S t).length)
```
`canonAtB` is *set-valued* in the step (`filter` over `range 6`) and only
counts `usedBefore`; both are invariant under rotating steps (L4.14) — this
is what makes the campaign's min-first shapes and the un-rotated witness
steps interchangeable.

**L3.8** `firstOcc_append : firstOcc (A ++ B) = firstOcc A ++ firstOcc (B.filter (· ∉ firstOcc A))`
(+ `mem_firstOcc`, `firstOcc_nodup`, `firstOcc_sublist`). ~80 lines.

**L3.9** `partOrder_perm : (∀ st ∈ S, WFStep st) → (partOrder S).Perm idRow6`. ~40 lines.

**L3.10** `newMen_relabel : newMen (relabelSched σ S) t = (newMen S t).map (app σ)`. ~40 lines.

**L3.11** `firstApp_relabel`
```lean
theorem firstApp_relabel {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) (t : Nat) :
    canonAtB (relabelSched (sigmaOf S) S) t = true
```
~130 lines. **Fiddliest lemma of §3.**

### 3.4 The bridge at the relabeled schedule (file `RelabelSched6.lean`, end)

Do not transport counts through `readoffS`. Instantiate
`count_le_of_orderPreserving` with `I := relabel6 σ J`, `J := readoffS S'`.

**L3.12** `stab_relabel6`
```lean
theorem stab_relabel6 {σ : List Nat} (hp : σ.Perm idRow6) {J : Inst6}
    {m w : Nat} (hm : m < 6) (hw : w < 6) :
    stab (relabel6 σ J) (app σ m) (app σ w) = stab J m w
```
~60 lines.

**L3.13–L3.15** relabeled versions of `readoffS_mrank_mono/top`,
`readoffS_wrank_mono` (with `S' := relabelSched σ (chainSched J)`), as in
revision 1. ~45 + ~40 + ~50 lines.

**L3.16** `sc_le_readoffS_relabelSched`
```lean
theorem sc_le_readoffS_relabelSched {J : Inst6} (hWF : WF6 J = true) (hne : sms6 J ≠ [])
    (hmo : manOpt J = idRow6) {σ : List Nat} (hp : σ.Perm idRow6) :
    stableCount6 (relabel6 σ J)
      ≤ stableCount6 (readoffS (relabelSched σ (chainSched J)))
```
~20 lines. Count chain used by the main theorem:
`49 ≤ sc I = sc J` (`stableCount6_wrelabel6`) `= sc (relabel6 σ J)` (`stableCount6_relabel6`) `≤ sc (readoffS S')` (L3.16).

### 3.5 Cubes (file `Cubes6.lean`) — mirrors `cube_campaign.py` exactly

Cubes carry **shapes**, not indices (the cube id `"0,1;2,3"` *is* the
prefix list); `prefixUnits` takes shapes and does the `idxOf … + 1`
itself, so no `cyclicShapes 6` Nodup fact is ever needed.

```lean
open SchedCNF6

/-- Well-formedness the formula needs (see §0, aliasing of `prefixUnits`/`sVar`). -/
def CubeWF (c : Cube) : Prop :=
  c.steps.length ≤ 15 ∧ (c.stopped = true → c.steps.length < 15) ∧
  ∀ sh ∈ c.steps, sh ∈ cyclicShapes 6

def legalPrefixB (S : List (List Nat)) : Bool          -- Bool mirror of apply_step's checks (§5.3)
def canonNextB (L : List (List Nat)) (sh : List Nat) : Bool :=
  canonAtB (L ++ [sh]) L.length && legalPrefixB (L ++ [sh])

/-- `split_children(prefix, closed=False)`: the stop child first, then the
rule-(a) canonical one-step extensions in `cyclicShapes 6` order.
Only meaningful for open cubes with `steps.length < 15` (§0). -/
def extendCanon (c : Cube) : List Cube :=
  ⟨c.steps, true⟩ ::
  ((cyclicShapes 6).filter (canonNextB c.steps)).map (fun sh => ⟨c.steps ++ [sh], false⟩)

/-- `root_cubes(2)` in the driver's order: `stop`; `s1;stop` for each
canonical `s1`; then the open depth-2 prefixes `s1;s2`. -/
def canonicalCubes2 : List Cube :=
  let l1 := (cyclicShapes 6).filter (canonNextB [])
  ⟨[], true⟩ :: (l1.map fun s1 => ⟨[s1], true⟩) ++
  (l1.flatMap fun s1 =>
    ((cyclicShapes 6).filter (canonNextB [s1])).map fun s2 => ⟨[s1, s2], false⟩)
-- expected: 1 + 153 + 25,339 = 25,493 cubes, the same ids as `cube_campaign.py --count`

def Fits (c : Cube) (S : List (List Nat)) : Prop :=
  c.steps = (S.take c.steps.length).map minFirst ∧
  c.steps.length ≤ S.length ∧
  (c.stopped = true → S.length = c.steps.length)
```

**L3.17** `cube_of_canonical`
```lean
theorem cube_of_canonical {S : List (List Nat)} (hL : Legal S)
    (hcan : ∀ t, canonAtB S t = true) :
    ∃ c ∈ canonicalCubes2, Fits c S
```
Cases `S = []` (the `stop` cube), `[s1]` (`⟨[minFirst s1], true⟩`),
`s1 :: s2 :: _` (`⟨[minFirst s1, minFirst s2], false⟩`). Membership in the
filtered lists needs, for `L := (S.take d).map minFirst`, `d ∈ {1, 2}`:
* `minFirst s_i ∈ cyclicShapes 6` — L4.11;
* `canonAtB L (d-1) = true` — from `hcan (d-1)` via `canonAtB_take` (L3.21)
  and `canonAtB_map_minFirst` (L4.14);
* `legalPrefixB L = true` — from `Legal_take` (L5.11), then **`Legal_map_minFirst`
  (L4.13)**, then `legalPrefixB_of_Legal` (L5.12).
Revision 1 filtered the children by min-first shapes but discharged
legality on the un-rotated `S.take 2`; the rotation-invariance lemmas
close that gap. ~90 lines.

**L3.18** adaptive splitting (the campaign splits timeouts to depth 3/4):
```lean
def refineCubes (cs : List Cube) (split : Cube → Bool) : List Cube :=
  cs.flatMap (fun c =>
    if split c && !c.stopped && decide (c.steps.length < 15) then extendCanon c else [c])
theorem fits_refine {cs split c S} (hL : Legal S) (hcan : ∀ t, canonAtB S t = true)
    (hc : c ∈ cs) (hf : Fits c S) : ∃ c' ∈ refineCubes cs split, Fits c' S
```
The stop child of `extendCanon c` fits exactly when `S.length = c.steps.length`;
an open child `c.steps ++ [minFirst (S.getD c.steps.length [])]` fits when
`S.length > c.steps.length` (same three membership facts as L3.17, at depth
`c.steps.length + 1`). A 15-step open cube is never split (guard) — it is
already closed: `Fits` with `steps.length = 15 = S.length` by L2.6. ~70 lines.
The final theorem is stated for `refineCubes^n canonicalCubes2 split_i`,
with the split predicates recorded from the campaign journal as Lean list
literals of cube ids (§11).

**L3.19** `canonicalCubes2_WF : ∀ c ∈ canonicalCubes2, CubeWF c` and
**L3.20** `refineCubes_WF : (∀ c ∈ cs, CubeWF c) → ∀ c ∈ refineCubes cs split, CubeWF c`
(shapes come from `filter` over `cyclicShapes 6`; lengths ≤ 2 resp. +1
under the `< 15` guard; the stop child has `steps.length < 15` by the guard —
this is the fix for the `sVar L 15 0` collision). ~40 lines.

**L3.21** `canonAtB_take : t < d → canonAtB (S.take d) t = canonAtB S t`
(`canonAtB S t` only reads `S.take t` and `S.getD t`). ~20 lines.

## 4. The encoding and the assignment — on top of `SchedCNF6`

### 4.1 Variable layout = `SchedCNF6` (file exists; decode in new `Decode6.lean`)

Nothing new is defined for ids. With `L := layout 6`
(**L4.1** `layout6_eq : layout 6 = ⟨6, 15, 409, 720⟩`, by `rfl`/`decide`;
needs `(cyclicShapes 6).length = 409` and `(permsN 6).length = 720`, both
kernel evaluations — see risk 5), the existing offset functions evaluate
to (Python allocation order, `k` = number of selector slots):

| `SchedCNF6` name | meaning | id (n = 6) | range |
|---|---|---|---|
| `mVar L t m w` | `M[t][m][w]`, t ≤ 15 | `1 + 36t + 6m + w` | 1..576 |
| `vVar L t m w` | `V[t][m][w]`, t ≤ 15 | `577 + 36t + 6m + w` | 577..1152 |
| `sVar L t j` | `S[t][j]`, t < 15, j ≤ 409 (0 = stop, j = shape `SH[j-1]`) | `1153 + 410t + j` | 1153..7302 |
| `cVar L m a b t` | `C` aux of `before(m,a,b)`, a ≠ b, t ≤ 15 | `7303 + 17·(30m + opIdx 6 a b) + t` | 7303..10362 |
| `beforeVar L m a b` | `before(m,a,b)` = `cVar L m a b 16` | | (interleaved) |
| `neitherVar L m a b` | `neither(m,{a,b})`, a < b | `10363 + 15m + upIdx 6 a b` | 10363..10452 |
| `pmVar L m a b` | `PM(m,a,b)`, a ≠ b | `10453 + 30m + opIdx 6 a b` | 10453..10632 |
| `cWVar L w a b t` | `C` aux of `beforeW(w,a,b)` | `10633 + 17·(30w + opIdx 6 a b) + t` | 10633..13692 |
| `beforeWVar L w a b` | = `cWVar L w a b 16` | | (interleaved) |
| `pwVar L w a b i` | i=0 `PW(w,a,b)`, 1 `later`, 2 `only_a`, 3 `nv` (a<b only) | `13693 + 105w + pwOff 6 a b + i` | 13693..14322 |
| `yVar L t i` | `Y[t][i]`, t < k, i < 720 | `14323 + 720t + i` | 14323..14322+720k |
| `pfVar L k t i` | `Pf[t][i]` | `14323 + 720k + 720t + i` | ..14322+1440k |

`numVars L k = 14322 + 1440k` = 84,882 at k = 49 (matches Python). The
revision-1 table (`15942 + 1440k`, padded `a = b` slots) is withdrawn.

Decoding (the f(5) `tau` pattern: range tests, then `/` and `%`):

```lean
inductive V6
  | M (t m w : Nat) | Vis (t m w : Nat) | St (t j : Nat)
  | C (m a b t : Nat) | Bef (m a b : Nat) | Nei (m a b : Nat) | PM (m a b : Nat)
  | CW (w a b t : Nat) | BefW (w a b : Nat)
  | PW (w a b : Nat) | Later (w a b : Nat) | OnlyA (w a b : Nat) | NeiW (w a b : Nat)
  | Y (t i : Nat) | Pf (t i : Nat) | junk
/-- inverse tables for the pair indices of `SchedCNF6` -/
def upairs (n : Nat) : List (Nat × Nat)                 -- a < b in Python loop order
def pwTable : List (Nat × Nat × Nat) :=                  -- (a, b, i) in `pwVar` id order, length 105
  (opairs 6).flatMap fun ab => (List.range (pwWidth ab.1 ab.2)).map fun i => (ab.1, ab.2, i)
def dec6 (k : Nat) (v : Nat) : V6 :=
  if v = 0 then .junk
  else if v ≤ 576  then let u := v - 1;    .M (u / 36) (u % 36 / 6) (u % 6)
  else if v ≤ 1152 then let u := v - 577;  .Vis (u / 36) (u % 36 / 6) (u % 6)
  else if v ≤ 7302 then let u := v - 1153; .St (u / 410) (u % 410)
  else if v ≤ 10362 then let u := v - 7303; let g := u / 17; let ab := (opairs 6).getD (g % 30) (0, 0)
       if u % 17 = 16 then .Bef (g / 30) ab.1 ab.2 else .C (g / 30) ab.1 ab.2 (u % 17)
  else if v ≤ 10452 then let u := v - 10363; let ab := (upairs 6).getD (u % 15) (0, 0); .Nei (u / 15) ab.1 ab.2
  else if v ≤ 10632 then let u := v - 10453; let ab := (opairs 6).getD (u % 30) (0, 0); .PM (u / 30) ab.1 ab.2
  else if v ≤ 13692 then (as C/Bef, with .CW / .BefW, base 10633)
  else if v ≤ 14322 then let u := v - 13693; let abi := pwTable.getD (u % 105) (0, 0, 0)
       match abi.2.2 with | 0 => .PW (u/105) abi.1 abi.2.1 | 1 => .Later .. | 2 => .OnlyA .. | _ => .NeiW ..
  else if v ≤ 14322 + 720 * k then let u := v - 14323; .Y (u / 720) (u % 720)
  else if v ≤ 14322 + 1440 * k then let u := v - 14323 - 720 * k; .Pf (u / 720) (u % 720)
  else .junk
```

**L4.2** inverse-table lemmas (by `decide`, ≤ 105 cases each):
`opairs_getD_opIdx : a ≠ b → a < 6 → b < 6 → (opairs 6).getD (opIdx 6 a b) (0,0) = (a, b)` and `opIdx_lt : … < 30`;
`upairs_getD_upIdx : a < b → b < 6 → (upairs 6).getD (upIdx 6 a b) (0,0) = (a, b)` and `upIdx_lt : … < 15`;
`pwTable_getD : a ≠ b → a < 6 → b < 6 → i < pwWidth a b → pwTable.getD (pwOff 6 a b + i) (0,0,0) = (a, b, i)` and `pwOff_add_lt : … < 105`.
~40 lines.

**L4.3** twelve decode lemmas, one per offset function, each
`simp only [dec6, mVar, layout6_eq, …]` + `omega`/`Nat.div_add_mod` + the
table lemma (the f(5) `eval_prefVar_*` pattern):
```lean
theorem dec_mVar (ht : t ≤ 15) (hm : m < 6) (hw : w < 6) : dec6 k (mVar (layout 6) t m w) = .M t m w
theorem dec_vVar (ht : t ≤ 15) (hm) (hw) : dec6 k (vVar (layout 6) t m w) = .Vis t m w
theorem dec_sVar (ht : t < 15) (hj : j ≤ 409) : dec6 k (sVar (layout 6) t j) = .St t j
theorem dec_cVar (hm) (hab : a ≠ b) (ha) (hb) (ht : t ≤ 15) : dec6 k (cVar (layout 6) m a b t) = .C m a b t
theorem dec_beforeVar (hm) (hab) (ha) (hb) : dec6 k (beforeVar (layout 6) m a b) = .Bef m a b
theorem dec_neitherVar (hm) (hab : a < b) (hb) : … = .Nei m a b
theorem dec_pmVar (hm) (hab : a ≠ b) (ha) (hb) : … = .PM m a b
theorem dec_cWVar / dec_beforeWVar (…)  : … = .CW w a b t / .BefW w a b
theorem dec_pwVar (hw) (hab : a ≠ b) (ha) (hb) :
    dec6 k (pwVar (layout 6) w a b 0) = .PW w a b ∧ … 1 = .Later w a b ∧ … 2 = .OnlyA w a b ∧
    (a < b → … 3 = .NeiW w a b)
theorem dec_yVar (ht : t < k) (hi : i < 720) : dec6 k (yVar (layout 6) t i) = .Y t i
theorem dec_pfVar (ht : t < k) (hi : i < 720) : dec6 k (pfVar (layout 6) k t i) = .Pf t i
```
~12 × 20 = 240 lines. The range hypotheses are exactly the loop bounds of
the Python `build`, so every clause family supplies them for free.

**L4.4** `evalLit_pos : evalLit (τV ∘ dec6 k) (pos v) = τV (dec6 k v)`,
`evalLit_neg : … (neg v) = !τV (dec6 k v)` for `v ≠ 0` (`pos`/`neg` are
`SchedCNF6.pos/neg`; all ids ≥ 1). ~20 lines.

### 4.2 Shapes = `cyclicShapes 6`, min-first rotation (file `Shapes6.lean`)

The step list is `SchedCNF6.cyclicShapes 6` — sizes 2..6, `combos`
(itertools.combinations order) of men, `permsOf` (itertools.permutations
order) of the tail, head = least man. Revision 1's sublist-ordered
`shapes6` is withdrawn; the index `j` in `S[t][j]` is
`(cyclicShapes 6).idxOf sh + 1`, as in `prefixUnits`.

```lean
def rotateTo (st : List Nat) (x : Nat) : List Nat := st.drop (idxOf x st) ++ st.take (idxOf x st)
def minFirst (st : List Nat) : List Nat := rotateTo st (st.foldl min 6)
```

**L4.5** `mem_combos : l ∈ combos xs k ↔ l <+ xs ∧ l.length = k` (induction on
`xs`, generalizing `k`; the same statement as Mathlib's `mem_sublistsLen`
for a differently ordered enumeration). ~45 lines.

**L4.6** `mem_permsOf : xs.Nodup → (l ∈ permsOf xs ↔ l.Perm xs)` via
`mem_picks : (y, ys) ∈ picks xs ↔ ∃ i, xs[i] = y ∧ ys = xs.eraseIdx i`. ~70 lines.

**L4.7** `permsOf_nodup : xs.Nodup → (permsOf xs).Nodup` (also needed for
`permsN 6`, §4.3). ~45 lines.

**L4.8** `cyclicShapes6_length : (cyclicShapes 6).length = 409 := rfl`.

**L4.9** `applyStep_rotate : WFStep st → x ∈ st → applyStep (rotateTo st x) mu = applyStep st mu`
(cyclic successor is rotation-invariant). ~70 lines.

**L4.10** `minFirst_WFStep : WFStep st ↔ WFStep (minFirst st)` (Perm of a
rotation), `minFirst_head_min`, `minFirst_perm : (minFirst st).Perm st`. ~40 lines.

**L4.11** `minFirst_mem_cyclicShapes : WFStep st → minFirst st ∈ cyclicShapes 6`.
Structural (never `decide` over `st`): `men := (minFirst st).mergeSort (· ≤ ·)`
is sorted, Nodup, ⊆ `range 6` ⇒ `men <+ List.range 6` (sorted + Nodup +
subset of a sorted Nodup list ⇒ sublist) ⇒ `men ∈ combos (range 6) men.length`
(L4.5, `2 ≤ men.length ≤ 6` picks the `kk'` in `range 5`); head of
`minFirst st` = min = `men.headD 0`; tail is a `Perm` of `men.tail` ⇒ in
`permsOf men.tail` (L4.6, `men.tail` Nodup). Unfold `cyclicShapes` with
`List.mem_flatMap`/`mem_map`. ~80 lines.

**L4.12** `schedMatchings_map_minFirst` (**new**, requested by the critique)
```lean
theorem schedMatchings_map_minFirst {S : List (List Nat)} (hWF : ∀ st ∈ S, WFStep st) :
    schedMatchings (S.map minFirst) = schedMatchings S
```
`scanl` induction: each step `applyStep (minFirst st) mu = applyStep st mu`
by L4.9 with `x := st.foldl min 6 ∈ st` (`WFStep` ⇒ `st ≠ []`). ~30 lines.

**L4.13** `strajM_map_minFirst`, `strajW_map_minFirst` (rewrite by L4.12),
`Legal_map_minFirst : Legal S → Legal (S.map minFirst)` (and the converse,
via L4.10 both ways), `length_map_minFirst`. ~40 lines.

**L4.14** `canonAtB_map_minFirst : (∀ st ∈ S, WFStep st) → canonAtB (S.map minFirst) t = canonAtB S t`
(`newMen` of a rotated step is a `Perm` of the original — `filter` over a
`Perm` — so the `range 6`-filter and its length agree; `usedBefore` is the
length of `firstOcc` of a `Perm`-equivalent flatten, equal by
`firstOcc_nodup` + `mem_firstOcc` + `Perm.length_eq` via `perm_ext_iff_of_nodup`). ~60 lines.

### 4.3 Matchings = `permsN 6` (file `Shapes6.lean`, end)

The selector index `i` in `Y[t][i]` refers to `P[i]` with `P =
list(itertools.permutations(range(6)))` = `SchedCNF6.permsN 6`. This is
**not** the order of `idRow6.permutations` (Mathlib's `permutations`
enumerates differently); `sms6`/`stableCount6` are defined over
`idRow6.permutations`. The assignment's `idxs` are indices into `permsN 6`
and every `isStable6` fact is evaluated on `(permsN 6).getD i []`:

**L4.15** `permsN6_length : (permsN 6).length = 720 := rfl` (kernel evaluation, cf. `perms120_length`).

**L4.16** `mem_permsN6 : mu ∈ permsN 6 ↔ mu.Perm idRow6` (L4.6; `List.range 6 = idRow6` by `rfl`) and `permsN6_nodup` (L4.7). ~15 lines.

**L4.17** `permsN6_perm_permutations : (permsN 6).Perm idRow6.permutations`
(`List.perm_ext_iff_of_nodup` with `nodup_permutations`, `mem_permutations`, L4.16). ~15 lines.

**L4.18** `stableCount6_eq_filter_permsN : stableCount6 R = ((permsN 6).filter (isStable6 R)).length`
(`Perm.filter` + `Perm.length_eq`, unfolding `sms6`). ~10 lines.

### 4.4 Frames, visited masks, the assignment (files `Frames6.lean`, `Faithfulness6.lean`)

```lean
def frame (S : List (List Nat)) (t : Nat) : List Nat :=
  (schedMatchings S).getD (min t S.length) []          -- stop frames copy the last
def colM (S) (m) : List Nat := (schedMatchings S).map (fun mu => mu.getD m 0)
def vis (S) (t m w : Nat) : Bool := decide (w ∈ (colM S m).take (t + 1))   -- prefix union
def stepIdx (S) (t : Nat) : Nat :=
  if t < S.length then (cyclicShapes 6).idxOf (minFirst (S.getD t [])) + 1 else 0
```
`stepIdx` uses the same `idxOf … + 1` as `prefixUnits`, so cube units are
satisfied by definitional unfolding (§6.13).

The assignment (parameters: `S` legal with `S.length ≤ 15`, `idxs` the
sorted list of indices `i < 720` with `isStable6 (readoffS S) ((permsN 6).getD i [])`):

```lean
def befB (S) (m a b : Nat) : Bool := (List.range 16).any (fun t => vis S t m a && !vis S t m b)
def befWB (S) (w a b : Nat) : Bool := (List.range 16).any (fun t => vis S t a w && !vis S t b w)
def τV (S : List (List Nat)) (idxs : List Nat) : V6 → Bool
  | .M t m w      => decide ((frame S t).getD m 0 = w)
  | .Vis t m w    => vis S t m w
  | .St t j       => decide (j = stepIdx S t)
  | .C m a b t    => vis S t m a && !vis S t m b
  | .Bef m a b    => befB S m a b
  | .Nei m a b    => !vis S 15 m a && !vis S 15 m b
  | .PM m a b     => befB S m a b || (decide (a < b) && (!vis S 15 m a && !vis S 15 m b))
  | .CW w a b t   => vis S t a w && !vis S t b w
  | .BefW w a b   => befWB S w a b
  | .Later w a b  => befWB S w b a && vis S 15 a w
  | .OnlyA w a b  => vis S 15 a w && !vis S 15 b w
  | .NeiW w a b   => !vis S 15 a w && !vis S 15 b w
  | .PW w a b     => (befWB S w b a && vis S 15 a w) || (vis S 15 a w && !vis S 15 b w)
                     || (decide (a < b) && (!vis S 15 a w && !vis S 15 b w))
  | .Y t i        => decide (idxs.getD t 720 = i)
  | .Pf t i       => decide (idxs.getD t 720 ≤ i)
  | .junk         => false
def tau6 (k : Nat) (S) (idxs) : Nat → Bool := fun v => τV S idxs (dec6 k v)
```
Every derived variable is defined *by its gate formula* (with `F = 15`
spelled out as `List.range 16` and `vis S 15`), so the definitional clause
families are discharged by generic gate lemmas (§6); the semantic content is
concentrated in `PM_sem`/`PW_sem` (§5). Note `PM` for `a > b` has no
`neither` term in the Python (§6.7); the `decide (a < b) &&` factor makes
τV agree with both branches.

Frame semantics:

**L4.19** `frame_zero : frame S 0 = idRow6`; **L4.20** `frame_perm : (∀ st ∈ S, WFStep st) → (frame S t).Perm idRow6` (~25).
**L4.21** `frame_succ_step : t < S.length → frame S (t+1) = applyStep (S.getD t []) (frame S t)` (~40).
**L4.22** `frame_succ_stop : S.length ≤ t → frame S (t+1) = frame S t` (~10).
**L4.23** `stepIdx_le : Legal S → stepIdx S t ≤ 409` (L4.11 + `idxOf_lt_length` + L4.8) (~15).
**L4.24** `shape_of_stepIdx : t < S.length → (cyclicShapes 6).getD (stepIdx S t - 1) [] = minFirst (S.getD t [])` (`getD_idxOf` with L4.11) (~15).
**L4.25** `vis_succ : vis S (t+1) m w = (vis S t m w || decide ((frame S (t+1)).getD m 0 = w))` (~45).
**L4.26** `vis_full : S.length ≤ t → (vis S t m w = true ↔ w ∈ strajM S m)` (~25).
**L4.27** `vis_zero : vis S 0 m w = decide (m = w)` (~10).

## 5. The crux: derived comparisons = read-off ranks

### 5.1 Prefix-destutter toolkit (file `DestutterPrefix6.lean`, generic `α` with `DecidableEq`)

**L5.1** `destutter'_take_prefix`, **L5.2** `destutter_take_prefix : (l.take k).destutter (· ≠ ·) <+: l.destutter (· ≠ ·)`. ~45 lines.
**L5.3** `destutter_take_succ` (the destuttered prefix grows by 0 or 1 element at step `k`, by exactly `l[k]` iff `l[k] ≠ l[k-1]`). ~50 lines.
**L5.4** `destutter_take_lengths_cover : l ≠ [] → ∀ j, 1 ≤ j → j ≤ (l.destutter (≠)).length → ∃ t, t < l.length ∧ ((l.take (t+1)).destutter (≠)).length = j`. ~45 lines.
**L5.5** `mem_prefix_iff_idxOf_lt : d.Nodup → p <+: d → x ∈ d → (x ∈ p ↔ idxOf x d < p.length)` (~30).
**L5.6** `idxOf_reverse : l.Nodup → x ∈ l → idxOf x l.reverse = l.length - 1 - idxOf x l` (~35).
**L5.7** `idxOf_filter_range_lt : a ∈ f → b ∈ f → f = (List.range 6).filter p → (idxOf a f < idxOf b f ↔ a < b)` (~20).
**L5.8** `mem_take_destutter_iff : x ∈ (l.take k).destutter (≠) ↔ x ∈ l.take k` (~8).

### 5.2 No-revisit semantics

**L5.9** `noRevisit_sem`
```lean
theorem noRevisit_sem {S} (hL : Legal S) {t m w : Nat} (hm : m < 6) (ht : t < S.length)
    (hnew : (frame S (t+1)).getD m 0 = w) (hold : (frame S t).getD m 0 ≠ w) :
    vis S t m w = false
```
~45 lines. (The CNF has only the man-side no-revisit clause; faithfulness
only needs the clauses to hold under τ.)

### 5.3 Prefix legality (for the cube filter) — must equal `apply_step`

`cube_campaign.apply_step` rejects a child when: (i) `moves + k > 30`,
(ii) rule (a) fails, (iii) some man in the step has already made 5 moves,
(iv) a man revisits a woman, (v) a woman revisits a man. The Lean list
must produce the *same* 25,493 ids, so `legalPrefixB` mirrors (i), (iii),
(iv), (v) (rule (a) is `canonAtB`):

**L5.10** `schedMatchings_take : schedMatchings (S.take k) = (schedMatchings S).take (k+1)` (~30).
**L5.11** `Legal_take : Legal S → Legal (S.take k)` (~40).
**L5.12** `legalPrefixB` :=
`S.all WFStepB && decide ((S.map length).sum ≤ 30) && (range 6).all (fun m => (strajM S m).Nodup && (strajM S m).length ≤ 6) && (range 6).all (fun w => (strajW S w).Nodup)`
with `legalPrefixB_of_Legal : Legal S → legalPrefixB S = true` (Nodup from
`Legal`; the cap from L2.5; the budget from `moves_le_30` in L2.6). ~50 lines.
(At depth ≤ 4 the cap and budget never bind, so the sets would coincide
even without them; they are mirrored anyway so that the identity of the
Lean list with `cube_campaign.py --count` holds by construction, not by
an argument about depth.)

### 5.4 The two crux lemmas (file `ReadoffSem6.lean`)

**L5.13** `PM_sem`
```lean
theorem PM_sem {S} (hL : Legal S) (hlen : S.length ≤ 15) {m a b : Nat}
    (hm : m < 6) (ha : a < 6) (hb : b < 6) (hab : a ≠ b) :
    τV S idxs (.PM m a b) = decide (idxOf a (rowOrderM S m) < idxOf b (rowOrderM S m))
```
Four cases on `a ∈ strajM`, `b ∈ strajM`, as in revision 1 (L5.4 with
`j := idxOf b d` and `t ≤ S.length ≤ 15`; `t = 15` frame = full trajectory by L4.26). ~120 lines.

**L5.14** `visW_iff : (∀ st ∈ S, WFStep st) → w < 6 → a < 6 → (vis S t a w = true ↔ a ∈ ((schedMatchings S).map (fun mu => idxOf w mu)).take (t+1))`. ~35 lines.

**L5.15** `PW_sem`
```lean
theorem PW_sem {S} (hL : Legal S) (hlen : S.length ≤ 15) {w a b : Nat}
    (hw : w < 6) (ha : a < 6) (hb : b < 6) (hab : a ≠ b) :
    τV S idxs (.PW w a b) = decide (idxOf a (rowOrderW S w) < idxOf b (rowOrderW S w))
```
`rowOrderW = (strajW S w).reverse ++ filter`; L5.6 turns "earlier in
reverse" into "later in `strajW`"; `Later w a b = BefW w b a ∧ Vis 15 a w`. ~130 lines.

## 6. Clause families: `SchedCNF6`'s twelve definitions, one satisfaction lemma each

Conventions: `L := layout 6` (rewritten to `⟨6, 15, 409, 720⟩` by L4.1 at
the start of every proof), `k` = number of slots (49 in production, 48 for
the positive control), `τ := tau6 k S idxs`. Statement pattern (as in
`Faithfulness.lean`): `(family L …).all (evalClause τ) = true` under
`hL : Legal S`, `hlen : S.length ≤ 15`, plus selector hypotheses where
relevant. Since the families are `flatMap`/`filterMap` over `List.range`,
each proof opens with `simp only [List.all_flatMap, List.all_append,
List.all_map, List.all_filterMap, List.all_range_iff, …]` and then works
per clause with L4.3/L4.4. **No family is redefined**; the definitions
under proof are `SchedCNF6.initClauses`, …, `SchedCNF6.blockClauses` verbatim.

Generic gate lemmas (~50 lines, stated on the literal patterns that occur
inside the definitions, not as new clause constructors):
```lean
theorem and2_sat (hx : evalLit τ x = (evalLit τ y && evalLit τ z)) :
    ([[-x, y], [-x, z], [x, -y, -z]]).all (evalClause τ) = true        -- C, later, only_a, nv, neither
theorem or_sat (hx : evalLit τ x = ys.any (evalLit τ)) :
    ((ys.map fun y => [-y, x]) ++ [(-x) :: ys]).all (evalClause τ) = true -- before, beforeW, PM, PW
```
(with `x, y, z ≠ 0`, `∀ y ∈ ys, y ≠ 0` so that `evalLit τ (-l) = !evalLit τ l`.)

1. **`initClauses L`** — `init_sat`: `dec_mVar`/`dec_vVar` at `t = 0`, L4.19, L4.27. ~25 lines.
2. **`matchingClauses L`** (t ≤ 15) — `matching_sat`: L4.20 ⇒ row value exists and is unique; columns by `perm6_getD_inj`. ~50 lines.
3. **`stepClauses L`** (t < 15: `[sVar t 0..409]`, AMO, absorb `[-sVar t 0, sVar (t+1) 0]` if t+1 < 15) — `step_sat`: `stepIdx S t ≤ 409` (L4.23) picks the true literal; AMO from `decide (j = stepIdx)`; absorb: `¬ t < len ⇒ ¬ t+1 < len`. ~40 lines.
4. **`transitionClauses L (cyclicShapes 6)`** — assembled from four sub-lemmas per `t < 15`:
   * `stopTrans_sat` (`[-sVar t 0, -mVar t m w, mVar (t+1) m w]`): `sVar t 0` true ⇒ `t ≥ len` ⇒ L4.22. ~20 lines.
   * `shapeClauses_sat` for `j' < 409`, `sh := (cyclicShapes 6).getD j' []`, on `SchedCNF6.shapeClauses L t (j'+1) sh`: if `sVar t (j'+1)` is true then `j'+1 = stepIdx S t`, so `t < len` and `sh = minFirst (S.getD t [])` (L4.24); `frame (t+1) = applyStep (S_t) (frame t)` (L4.21) `= applyStep sh (frame t)` (L4.9); `applyStep_getD` gives both clause shapes (`idxOf a sh = i` and `sh.getD ((i+1) % kk) 0 = b` from Nodup of `sh` — `minFirst_WFStep`; `sh.contains m = false ⇒ m ∉ sh`). ~110 lines (**largest family lemma**).
   * `noRevisit_sat` (`[-mVar (t+1) m w, mVar t m w, -vVar t m w]`): `t < len` L5.9; `t ≥ len` L4.22. ~35 lines.
   * `visUpdate_sat` (three clauses): L4.25. ~35 lines.
   * `transition_sat`: `List.all_append` of the four. ~15 lines.
5. **`beforeClauses L`** (`a ≠ b`; `C` ids `cVar L m a b t`, t ≤ 15; `bv = beforeVar`) — `before_sat`: `and2_sat` with `dec_cVar`/`dec_vVar`, `or_sat` with `dec_beforeVar`; `befB` is literally `(range 16).any`. ~40 lines.
6. **`neitherClauses L`** (`a < b`, `vVar L 15 _ _`) — `neither_sat`: `and2_sat`, `dec_neitherVar`. ~15 lines.
7. **`pmClauses L`** — `pm_sat`: `a < b`: `or_sat` over `[bv, nv]`; `a > b`: the two clauses `[-bv, p], [-p, bv]` (τV's `decide (a < b) && …` factor is `false`). ~30 lines.
8. **`beforeWClauses L`** — as 5 with `vVar L t a w`, `vVar L t b w`, `dec_cWVar`/`dec_beforeWVar`. ~30 lines.
9. **`pwClauses L`** (`later = pwVar … 1`, `only_a = … 2`, `nv = … 3` iff `a < b`, `p = … 0`, `terms`) — `pw_sat`: three `and2_sat` (`Later`: `beforeWVar L w b a` decodes with `b ≠ a`; `OnlyA`; `NeiW` if `a < b`), then `or_sat` over `terms`; `dec_pwVar`. ~50 lines.
10. **`selectorClauses L k`** (`[yVar t 0..719]`; `[-Y, Pf]`; ladder-internal `[-Pf(i-1), Pf i]`, `[-Pf i, Pf(i-1), Y i]`, `[-Pf 0, Y 0]`) — `selector_sat (hlen : k ≤ idxs.length) (hmem : ∀ i ∈ idxs, i < 720)`: nonempty as f(5) `nonempty_sat`; the rest is arithmetic on `idxs.getD t 720 ≤ i`. ~70 lines.
11. **`ladderClauses L k`** (`t < k-1`: `[-yVar (t+1) 0]`, `j ≥ 1`: `[-yVar (t+1) j, pfVar k t (j-1)]`) — `ladder_sat (hlen) (hpair : idxs.Pairwise (· < ·))`: `idxs[t] < idxs[t+1] = j ⇒ idxs[t] ≤ j-1`; `idxs[t+1] ≥ 1`. ~40 lines.
12. **`blockClauses L k (permsN 6)`** (`t < k`, `i < 720`, `mu := (permsN 6).getD i []`, `m`, `w ≠ mu.getD m 0`: `[-yVar t i, -pmVar m w (mu.getD m 0), -pwVar w m (invOf mu w) 0]`) — `block_sat (hL) (hlen) (hstab : ∀ i ∈ idxs, i < 720 ∧ isStable6 (readoffS S) ((permsN 6).getD i []) = true)`: mirror of f(5) `block_sat` with `eval_prefLit_*` replaced by **L5.13/L5.15 + `get2_readoffS_mrank/wrank`**; `mu.Perm idRow6` from L4.16 (`getD` of a member, `permsN6_length`), so `invOf mu w = idxOf w mu < 6` and `mu.getD m 0 ≠ w` supply the `a ≠ b` side conditions of `dec_pmVar`/`dec_pwVar`; then the `(m, w)` case of `isStable6 (readoffS S) mu`. ~100 lines.
13. **`prefixUnits 6 c.steps`** — `prefixUnits_sat (hWFc : CubeWF c) (hf : Fits c S)`: unit `t` is `pos (sVar L t ((cyclicShapes 6).idxOf (c.steps.getD t []) + 1))`; from `Fits`, `c.steps.getD t [] = minFirst (S.getD t [])` and `t < c.steps.length ≤ S.length`, so the id decodes (`dec_sVar`: `t < 15` from `hlen`, `j ≤ 409` from L4.11 + `idxOf_lt_length`) to `.St t (stepIdx S t)`, true by `rfl`. ~30 lines.
14. **`stopUnits 6 c.steps c.stopped`** (new, §4.1) — `stopUnits_sat (hWFc) (hf)`: if stopped, `t := c.steps.length = S.length < 15` (`CubeWF`), the unit is `sVar L t 0`, `stepIdx S t = 0` since `¬ t < S.length`. ~20 lines.

**Addition** (realized in `Cubes6.lean`, namespace `Cubes6`, with the
signature `cubeCNFc (n k : Nat) (c : Cube)`; ~12 lines):
```lean
/-- `cube_campaign.cube_units(...)`: after the prefix units, `S[len(prefix)][0]` iff closed. -/
def stopUnits (n : Nat) (pre : List (List Nat)) (closed : Bool) : List (List Int) :=
  if closed then [[pos (sVar (layout n) pre.length 0)]] else []
/-- `build(n, k)` + `cube_units(prefix, closed)`: the per-cube file the campaign writes. -/
def cubeCNFc (n k : Nat) (pre : List (List Nat)) (closed : Bool) : List (List Int) :=
  schedCNFn n k ++ prefixUnits n pre ++ stopUnits n pre closed
```
`cubeCNFn n k pre = cubeCNFc n k pre false` (rfl). **Addition to
`ExportSchedCnf.lean`** (~6 lines): a `--stop` flag selecting
`cubeCNFc n k pre true`. Byte-identity of `export_sched_cnf --k=49
--prefix=… [--stop]` with the worker's `c_*.cnf` (header
`p cnf 84882 (2709212 + #units)`, body, units in the same order) is to be
checked on `0,1;2,3`, `0,1;stop` and `stop` before the campaign starts
(§9, §11).

## 7. Assembly (file `Faithfulness6.lean`, end; `Bridge6.lean`)

**L7.1** `campaign_faithful` (statement in §0). Proof skeleton (~100 lines):
```
hne  : sms6 I ≠ []                                     (stableCount6 I ≥ 49)
J, hWFJ, hmo, hneJ, hcntJ                              (as in validity_unconditional)
S  := chainSched J;  hLS := Legal_chainSched hWFJ hneJ hmo
σ  := sigmaOf S;     hp := invMatch_perm (partOrder_perm hLS.1)
S' := relabelSched σ S;  hL' := Legal_relabel hp hLS;  hlen' : S'.length ≤ 15 (L2.6 + L3.7)
hcan : ∀ t, canonAtB S' t = true                       (L3.11)
⟨c, hc, hfit⟩ := cube_of_canonical hL' hcan            (L3.17);  hWFc := canonicalCubes2_WF c hc (L3.19)
h49' : 49 ≤ stableCount6 (readoffS S')                 (§3.4 chain)
R    := readoffS S'
idxs := (List.range 720).filter (fun i => isStable6 R ((permsN 6).getD i []))
hcount : idxs.length = stableCount6 R                  (filter-over-range-of-getD, as f5, + L4.18)
hlen : 49 ≤ idxs.length;  hpair : idxs.Pairwise (· < ·) (pairwise_lt_range.filter);  hmem; hstab
exact ⟨tau6 49 S' idxs, by
  unfold cubeFormula cubeCNFc schedCNFn; rw [layout6_eq]
  simp only [evalCNF, List.all_append]; exact ⟨…12 family lemmas…, prefixUnits_sat, stopUnits_sat⟩⟩
```

**L7.2** `f6_upper_of_unsat`
```lean
theorem f6_upper_of_unsat (H : ∀ c ∈ canonicalCubes2, ¬ Satisfiable (cubeFormula 49 c)) :
    ∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48
```
and **L7.3** the `refineCubes` variant for the cube list the campaign
actually ran (`H : ∀ c ∈ refineCubes (refineCubes canonicalCubes2 split3) split4, …`),
using L3.18/L3.20. ~40 lines. **L7.4** `f6_eq_48_of_unsat` additionally
needs the dihedral lower bound `stableCount6 dihedral6 = 48` (a
`decide`/`stableCount'`-style kernel computation as in `Lower.lean`; 720 ×
36 pair checks; not part of faithfulness proper). ~40 lines.

**Printer**: `export_sched_cnf` (exists) + `--stop`. A second small
executable `export_cubes6` (~30 lines, trusted) prints `canonicalCubes2`
(and `refineCubes` lists) as cube ids, one per line, in the driver's id
syntax, for the set comparison in §9.

## 8. Size estimate and dependency order

> **Erratum (recheck 2026-09-03):** L4.14 `canonAtB_map_minFirst` is stated in terms of `canonAtB`/`newMen`/`usedBefore`/`firstOcc` (FirstApp6) and therefore belongs in `FirstApp6.lean` (right after `canonAtB`; needs only `minFirst_perm` from Shapes6 and the `firstOcc` lemmas L3.8), not in `Shapes6.lean`. Adjust the table: Shapes6 = L4.5–L4.13 (≈460 lines), FirstApp6 += L4.14 (≈350 lines).

| # | file | status | content | lemmas | lines |
|---|---|---|---|---|---|
| 0 | `SchedCNF6.lean` | **exists** (584) | formula; add `stopUnits`, `cubeCNFc` | 0 | +12 |
| 0' | `ExportSchedCnf.lean` | **exists** (44) | printer; add `--stop` | 0 | +6 |
| 1 | `Shapes6.lean` | new | `mem_combos`, `mem_permsOf`, `permsOf_nodup`, `rotateTo`/`minFirst`, L4.5–L4.14, `permsN 6` lemmas L4.15–L4.18 | 15 | 520 |
| 2 | `Decode6.lean` | new | `V6`, `upairs`, `pwTable`, `dec6`, L4.1–L4.4 | 18 | 370 |
| 3 | `DestutterPrefix6.lean` | new | L5.1–L5.8 | 8 | 240 |
| 4 | `SchedLen6.lean` | new | L2.1–L2.6 (+ `moves_le_30`) | 6 | 240 |
| 5 | `Frames6.lean` | new | `frame`/`vis`/`stepIdx`, L4.19–L4.27, L5.9–L5.12 | 13 | 340 |
| 6 | `ReadoffSem6.lean` | new | L5.13–L5.15 | 3 | 290 |
| 7 | `RelabelSched6.lean` | new | L3.1–L3.7, L3.12–L3.16 | 12 | 520 |
| 8 | `FirstApp6.lean` | new | `firstOcc`/`partOrder`/`sigmaOf`/`canonAtB`, L3.8–L3.11 | 4 (+3 small) | 290 |
| 9 | `Cubes6.lean` | new | `Cube`, `CubeWF`, `extendCanon`, `canonicalCubes2`, `Fits`, `refineCubes`, L3.17–L3.21 | 5 | 230 |
| 10 | `Faithfulness6.lean` | new | `τV`/`tau6`, gate lemmas, 12 family lemmas (+5 sub-lemmas), 2 unit lemmas, L7.1 | 22 | 1,120 |
| 11 | `Bridge6.lean` | new | L7.2–L7.4, lower bound | 3 | 100 |
| 12 | `ExportCubes6.lean` | new | cube-id printer (trusted) | 0 | 30 |
| | **total** | | | **≈ 109** | **≈ 4,300** |

Withdrawn from revision 1: `Encoding6.lean` (closed-form layout, `enc`/`dec`,
16 redefined families), `ExportCnf6.lean` (new printer), the sublist-ordered
`shapes6`, `perms720 := idRow6.permutations`. None of these existed on disk.

Honest note: the f(5) file was 429 lines for 6 families; here 12 families
with 5 sub-lemmas, the schedule semantics, a decode layer for a 12-block
allocation-order layout, and the enumeration lemmas for `combos`/`permsOf`
that a closed-form layout would have avoided. 3,800–4,800 is the realistic
band; the price of certificate compatibility is roughly +600 lines over
revision 1's estimate.

Dependency order (build order; each item only needs the ones above it):

0. `SchedCNF6` (+12 lines) · 1. `Shapes6` (SchedCNF6, Sched6, SixBridge) ·
2. `Decode6` (SchedCNF6) · 3. `DestutterPrefix6` (generic) ·
4. `SchedLen6` (Sched6) · 5. `Frames6` (1, 3, 4) · 6. `ReadoffSem6` (3, 5, ValidityBridge6) ·
7. `RelabelSched6` (Sym6, ChainSched6, ValidityBridge6) · 8. `FirstApp6` (1, 7) ·
9. `Cubes6` (1, 5, 8) · 10. `Faithfulness6` (all) · 11. `Bridge6` (10, WRelabel6) ·
12. `ExportCubes6` (9).

Suggested execution order to de-risk early: 0 (+ `--stop`) → byte-identity
check of the three cube files (§6) → 9 + 12 (cube list) → **set comparison
with `cube_campaign.py --count`/root ids (must be 25,493 identical ids)** →
positive control (k = 48 with the dihedral schedule pinned via a
15-unit `--prefix` cube of its shapes plus `--stop`; expect SAT in < 1 s,
decode-recount 48) **before** any proof beyond L4.1; then 2 (decode
lemmas — mechanical, but they gate everything) → 3 → 5 → 6 (the crux) → 4
→ 1 → 10 (families) → 7 → 8 → 9 → 11.

## 9. Residual trust base after the campaign

Exactly the f(5) base, item for item (`VERIFYING.md` §"What you end up trusting"):

1. Lean 4 kernel (+ optionally `lean4checker`); axioms `propext`,
   `Classical.choice`, `Quot.sound` (`#print axioms f6_upper_of_unsat`).
2. The ~45 lines of *definitions* that state the problem: `Inst6`, `WF6`,
   `isStable6`, `sms6`, `stableCount6` (`SixBridge.lean`). Everything else
   (schedules, read-offs, relabels, `SchedCNF6`'s formula, the cube list)
   is proved about, not trusted.
3. One LRAT checker: `cake_lpr` (verified to machine code). `kissat` and
   `drat-trim` are **not** trusted (they only produce the certificate).
4. The DIMACS printer `ExportSchedCnf.lean` (44 + 6 lines, read it) and the
   cube-id printer `ExportCubes6.lean` (30 lines), and the **file identity**
   between what Lean prints and what `cake_lpr` checked. Certificates are
   valid only for the byte-identical `SchedCNF6` formula: a per-cube file
   is `header ‖ body(schedCNFn 6 49) ‖ units(c)`; the identity claim is
   `sha256(worker's c_*.cnf) = sha256(export_sched_cnf --k=49 --prefix=… [--stop])`.
   The driver currently records only `cnf_bytes`; it **must** record
   `cnf_sha256` per cube in the journal (files are deleted after checking),
   and the manifest must pair every `s VERIFIED UNSAT` with that hash,
   exactly as `f5/cubesL/cubesL_results.txt`. Reproduction: re-export every
   cube from Lean and compare hashes (25k exports; measure the exporter —
   if too slow, add a `--units-only` mode and hash `body ‖ units` with the
   body's hash `28421fb6…`-derived constant checked once).
5. That the cube set fed to the campaign is `canonicalCubes2` (or its
   recorded `refineCubes` refinement) **as printed by Lean**: the driver
   may keep generating ids in Python, but the campaign is complete only when
   the set of journaled verified ids equals the Lean-printed set (an
   `--audit` against `cubes2.txt`, not against `root_cubes(2)`).

Not trusted: `gen_enum.c`, `sched_sat.py`, `cube_calibrate.py`,
`cube_campaign.py`'s cube generation, the solver runs, and this plan. The
hypothesis `∀ c ∈ cubes, ¬ Satisfiable (cubeFormula 49 c)` remains outside
the kernel, discharged by the certificates, as in `f5_upper_of_unsat`.

## 10. Risks (ranked)

1. **Cube-list identity.** The Lean `canonicalCubes2` must equal the
   driver's `root_cubes(2)` as a set of ids (and per split, `extendCanon`
   = `split_children`). `legalPrefixB` mirrors `apply_step` including cap
   and budget (§5.3) so the identity holds by construction; verify by the
   printed-list comparison before launching (§8). A mismatch is a plan
   error, not a soundness error, but it would void the theorem's hypothesis.
2. **`firstApp_relabel` (L3.11) bookkeeping** — list-of-lists, `firstOcc`,
   `take`/`flatten` interplay; the most likely place for a 2–3× line overrun.
3. **`shapeClauses_sat` (family 4)** — index gymnastics (`idxOf a sh = i`,
   cyclic successor, `minFirst` rotation, `frame_succ_step`); largest single lemma.
4. **Decode lemmas (L4.3).** Twelve arithmetic inversions over a
   12-block layout with interleaved `before`/`C` ids (stride 17) and the
   variable-width `pw` groups; `omega` should handle each once the table
   lemmas are in place, but `pwOff` (a `takeWhile` sum) must be *evaluated*,
   not reasoned about — hence the `decide`d `pwTable_getD`.
5. **Kernel-computation cost.** `layout6_eq` needs `(cyclicShapes 6).length
   = 409` and `(permsN 6).length = 720` by `rfl`/`decide` (evaluating
   `combos`/`permsOf`; 720 six-element lists — cf. `perms120_length`, 120
   lists, which was fine); `pwTable_getD` (105 cases). Never `decide`
   membership in `canonicalCubes2` or evaluate `schedCNFn` inside a proof.
   The order-6 lower-bound `decide` (720 × 36) may need the `stableCount'`
   reformulation.
6. **PM/PW boundary cases** — the `t = 15` frame must coincide with "full
   trajectory" (`vis_full` needs `S.length ≤ 15`), women's reversed order,
   `a = b` excluded everywhere (`a ≠ b` hypotheses in every family touching PM/PW).
7. **`prefixUnits` aliasing.** `idxOf` of an unknown shape aliases to the
   next frame's stop; `sVar L 15 0` collides with `cVar L 0 0 1 0`. Carried
   as `CubeWF` hypotheses (proved for the Lean lists, L3.19/L3.20); the
   *driver* must never be given a hand-written cube id outside the Lean list.
8. **Adaptive splitting bookkeeping** (L3.18): the final cube list must be
   reproducible in Lean from the recorded split decisions; keep the split
   list small (depth-3 children of ~1,850 cubes ≈ 130k cubes is fine as a
   printed list).
9. Mathlib name churn (`List.map_destutter`, `destutter'_cons_pos`,
   `pairwise_lt_range`, `perm_ext_iff_of_nodup`, `nodup_permutations`) —
   check at v4.33.1 before relying on the exact forms.

## 11. Open questions (for the orchestrator)

1. **Cube list identity check now?** Run `export_cubes6` vs
   `cube_campaign.py --count` ids before proofs (plan says yes, §8); any
   difference is fixed on the Lean side by adjusting `legalPrefixB`, never
   by changing the driver's set after cubes have been verified.
2. **Journal `cnf_sha256`** (§9.4): add it to `run_cube` before launching at
   scale (one line: hash the bytes written). Without it the file identity
   for deleted cubes cannot be re-established.
   **Resolved 2026-09-03:** implemented — `cube_campaign.py` journals a header with `base_sha256` (= the Lean exporter's 28421fb6…), per-cube `cnf_sha256` (hashed before kissat) and `lrat_sha256`, and `--audit --expect-cnf-dir DIR` re-derives/compares hashes cube by cube against Lean-printed files.
3. `k` as a parameter of `cubeFormula` (k = 48 positive control, as
   `cubeCNF16` in f5) — assumed yes; `schedCNFn 6 48` is what
   `export_sched_cnf --k=48` prints.
4. Depth-3/4 splitting: record split decisions as a Lean literal list of
   cube ids, or restate the theorem per campaign run? Plan assumes a literal
   list + `refineCubes` (L3.18, L7.3).
5. Rule (b): the campaign uses rule (a) only, and so does the proof. For
   the record (§0): rule (b)-lex (`cube_calibrate.py`) is vacuous at depth 2
   under rule (a); rule (b)-index (`gen_enum.c`, size-first step indices) is
   not, and explains the 1,818,512 vs 1,833,929 depth-3 counts; both prunings
   are sound but neither is formalized, and no cube list in this plan depends
   on either. The witness orbits are min-first before relabeling
   (`stepDecompAux` scans `idRow6` in order); after σ they are not, so
   `minFirst` (L4.12–L4.14) is genuinely needed and is not a symmetry rule.
6. Is a woman-side no-revisit clause family wanted in the CNF? **No longer
   an option** without re-running the campaign: the formula is frozen at
   `SchedCNF6.schedCNFn 6 49` (sha `28421fb6…`). Adding clauses would
   invalidate every certificate produced so far.
7. Lower bound at order 6 in Lean (`stableCount6 dihedral6 = 48`) — is it
   already planned elsewhere? Needed for `f6_eq_48_of_unsat`, not for
   faithfulness.
8. Exporter throughput for the 25k-cube hash reproduction (§9.4): measure
   `export_sched_cnf` on one cube; decide between full re-export and a
   `--units-only` mode.
