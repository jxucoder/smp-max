# Finish plan (2026-09-08)

Archived: every item is done; paths in the body refer to the tree before the 2026-09-09 restructure (`lean/` is now `lean/`), see `docs/history/README.md`.

## Status (2026-09-08, evening)

- **A done.** `f6_eq_48_of_unsat` (`Bridge6.lean`) is proved: zero
  sorries, axioms `propext`, `Classical.choice`, `Quot.sound`; all 12 new
  files plus `SplitList6.lean` exist and build (faithfulness layer 19
  files, 4,761 lines, 333 theorems; reduction layer unchanged). The
  twelve families live in four files (`FamState6`, `FamTrans6`,
  `FamGates6`, `FamSelect6`); `block_sat` is named `block_sat6`.
- **B done.** All 321,492 journaled formula hashes re-hashed from
  Lean-printed pieces (`tools/campaign/verify_lean_hashes.py`); `finalCubes` = the 318,736
  verified ids; provenance and both checker builds recorded; the
  self-attested nature of the journal stated in CAMPAIGN.md, docs/verification.md,
  docs/results.md, README.md (`results/f6/campaign-2026-09-08/lean_identity.txt`).
- **C done**, including (2026-09-09) LICENSE (Apache-2.0), CITATION.cff,
  .zenodo.json, and the three PDFs rebuilt from the updated sources by the
  `build-papers` workflow. f(7) claims are backed by `results/f7/search/` (34 runs,
  2026-09-08). Publication steps that need the owner's accounts are listed
  in `docs/publishing.md`.
- **D done; E resolved** (risks 2 and 3 closed; the lower bound's
  `decide` ran without reformulation problems; no layer-0 definition
  changed).

Goal: make **f(6) = 48 a single kernel-checked Lean theorem whose only
hypothesis is the campaign's certificates**, close the remaining identity
checks between Lean and the journal, and bring every document and both
papers into line with that evidence. Written after the 2026-09-08 review
(`lake build`, axiom checks, exporter byte-identity, journal audit and
positive control all re-verified on this machine; nine-reviewer audit of
the Lean statements, encoding, cubes, docs, papers and f(7)).

## A. Lean: the order-6 faithfulness theorem

Target (replaces `campaign_faithful` of `docs/design/f6-faithfulness.md` §0 by
its `refineCubes` variant, L7.3):

```lean
-- SplitList6.lean (generated from the journal): the 1,804 depth-2 and 952
-- depth-3 cubes the campaign split, as cube-id literals.
def finalCubes : List Cube :=
  refineCubes (refineCubes canonicalCubes2 isSplitDepth2) isSplitDepth3
-- Faithfulness6.lean / Bridge6.lean
theorem f6_upper_of_unsat (H : ∀ c ∈ finalCubes, ¬ Satisfiable (cubeFormula 49 c)) :
    ∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48
theorem f6_eq_48_of_unsat (H : …) :
    (∀ I, WF6 I = true → stableCount6 I ≤ 48) ∧ ∃ I, WF6 I = true ∧ stableCount6 I = 48
```

`finalCubes` is printed by `export_cubes6 --final` and must equal, as a
set, the 318,736 `verified` ids of the journal (the leaves of the split
tree). That comparison is the cube-set identity; the per-cube formula
identity is item B.1.

Chain (every arrow a theorem): `49 ≤ sc I` → `J := wrelabel6 … I`
(`WF6 J`, `manOpt J = idRow6`, `sc J = sc I`) → `S := chainSched J`
(`Legal S`) → `σ := sigmaOf S`, `S' := relabelSched σ S` (`Legal S'`,
first-appearance canonical, `S'.length ≤ 15`) →
`sc (relabel6 σ J) ≤ sc (readoffS S')` (bridge re-instantiated at the
relabeled instance; `readoffS` is *not* relabel-equivariant and is never
assumed to be) → a cube `c ∈ finalCubes` with `Fits c S'` → `tau6 49 S'
idxs` satisfies `cubeFormula 49 c` → contradiction with `H`.

Files and lemmas (plan numbering from `docs/design/f6-faithfulness.md`; all
statements as written there unless noted). Layer 1 files depend only on
what exists today plus the definitions in `Cubes6.lean`/`RelabelSched6.lean`
added in step A.0; layer 2 depends on layer 1; layer 3 on everything.

| layer | file | content |
|---|---|---|
| 0 | `Cubes6.lean` (edit) | definitions `CubeWF`, `Fits`, `cubeFormula` |
| 0 | `RelabelSched6.lean` (new, def only) | `relabelSched σ S := S.map (·.map (app σ))`, `length_relabelSched` |
| 0 | `SplitList6.lean` (generated) | `splitDepth2`, `splitDepth3` (id literals), `isSplitDepth2/3`, `finalCubes` |
| 0 | `ExportCubes6.lean` (edit) | `--final` (print `finalCubes`), `--units=FILE` (print each cube's unit clauses) |
| 1 | `RelabelSched6.lean` | L3.1–L3.7 (`mapMu6_idRow6`, `applyStep_relabel`, `schedMatchings_relabel`, `strajM/W_relabel`, `Legal_relabel`), L3.12–L3.16 (`stab_relabel6`, relabeled `readoffS_*` order lemmas, `sc_le_readoffS_relabelSched`) |
| 1 | `FirstApp6.lean` | `partOrder`, `sigmaOf`; L3.8–L3.11 (`firstOcc_*`, `partOrder_perm`, `newMen_relabel`, `firstApp_relabel`); L4.14 `canonAtB_map_minFirst`; L3.21 `canonAtB_take` |
| 1 | `PrefixLegal6.lean` | L5.10–L5.12 (`schedMatchings_take`, `Legal_take`, `legalPrefixB_of_Legal`) |
| 1 | `FamState6.lean` | families 1–3: `init_sat`, `matching_sat`, `step_sat` |
| 1 | `FamTrans6.lean` | family 4: L5.9 `noRevisit_sem`, `stopTrans_sat`, `shapeClauses_sat`, `noRevisit_sat`, `visUpdate_sat`, `transition_sat` |
| 1 | `FamGates6.lean` | families 5–9: `before_sat`, `neither_sat`, `pm_sat`, `beforeW_sat`, `pw_sat` |
| 1 | `FamSelect6.lean` | families 10–12: `selector_sat`, `ladder_sat`, `block_sat`; L4.18 `stableCount6_eq_filter_permsN` and the index-list count lemma |
| 1 | `Units6.lean` | 13–14: `prefixUnits_sat`, `stopUnits_sat` |
| 1 | `Lower6.lean` | `dihedral6`, `WF6 dihedral6 = true`, `stableCount6 dihedral6 = 48` (kernel, via a `permutations'` reformulation as in `Lower.lean`) |
| 2 | `Coverage6.lean` | L3.17 `cube_of_canonical`, L3.18 `fits_refine`, L3.19 `canonicalCubes2_WF`, L3.20 `refineCubes_WF`, and `fits_final : Legal S → canonical S → ∃ c ∈ finalCubes, Fits c S ∧ CubeWF c` |
| 3 | `Faithfulness6.lean` | L7.1 `cube_faithful6` (assignment satisfies `cubeFormula 49 c`), the count chain, `f6_upper_of_unsat`, `f6_eq_48_of_unsat` |

Rules for every file: zero `sorry`, no new axioms, no `native_decide`, no
`implemented_by`; names and statements from the plan unless a deviation is
recorded in the file's header docstring; each file checked with
`lake env lean` before it is imported by `SmpMax.lean`.

Acceptance: `lake build` clean; `grep -rn sorry SmpMax/` empty;
`#print axioms f6_eq_48_of_unsat` = `[propext, Classical.choice, Quot.sound]`;
CI axiom list extended with `f6_upper_of_unsat`, `f6_eq_48_of_unsat`,
`cube_faithful6`, `fits_final`, `firstApp_relabel`, `Legal_relabel`.

## B. Certificate layer: close the identity checks

1. **All 321,492 cube formulas re-hashed from Lean.** `export_cubes6
   --units=ids.txt` prints each cube's unit clauses from `prefixUnits` /
   `stopUnits`; `tools/campaign/verify_lean_hashes.py` composes `header ‖ body ‖ units` with
   the Lean-exported base body (sha `28421fb6…`, already byte-identical to
   Python) and compares every journaled `cnf_sha256`. Replaces STATUS "next"
   item 3, which described a Lean-side check that the Python audit does not
   perform.
2. **Cube-set identity.** `export_cubes6 --final` vs the journal's verified
   ids: equal as sets, 318,736 each. Record the command and result in
   `docs/reference/campaign.md` and `docs/results.md`.
3. **Provenance.** Record per-host checker builds (arm64 `cake_lpr_arm8.S`
   `95b64883…`, x86-64 `cake_lpr.S` `2f3af32d…`) with the number of records
   each produced; correct "Mac mini alone covers the whole tree".
4. Keep the honest statement that the journal is self-attested: full
   independent verification means re-solving (≈300 core-hours); publish the
   per-cube hashes so a re-run can be compared record by record.

## C. Documents and papers

- `docs/results.md`: state the missing theorem in the right direction (instance
  → model), replace "7 of 12 files" and "Estimate: days" with the file table
  above and its status, fix the depth breakdown (must sum to 321,492), the
  provenance sentence, and the "next" list.
- `README.md`: top bullet and f(6) row carry the caveat until A lands, then
  say "single Lean theorem, certificates as hypothesis" and point to the
  identity checks.
- `docs/verification.md`: replace the 2026-09-01 f(6) section with the campaign
  recipe (gunzip, `--audit`, `export_cubes6 --final`, `lean_rehash.py`, the
  axiom list); fix the 240-file hash wording.
- `docs/history/research-retrospective.md`, `docs/history/research-notebook.md`, `docs/f6.md`, `docs/reference/campaign.md`,
  `docs/design/f6-faithfulness.md` header/progress log/§8 table: certificate
  campaign is the evidence, enumeration is corroboration.
- Papers: `papers/f6/f6-max-stable-matchings.tex` abstract, "Validation", "Lean" and outlook
  sections rewritten around the campaign + faithfulness theorem; Lemma
  "Symmetry soundness (ii)" restated at the schedule level (instance-level
  relabel + re-instantiated bridge, as proved); f(7) prior bound 81 (Ong et
  al. 2024) and 85 here; Lean counts refreshed. `papers/notes/f6-schedule-reduction.tex` and
  `papers/f5/f5-max-stable-matchings.tex`: CI wording, counts.
- `docs/f7.md`: full-budget and multi-seed claims either backed by
  committed logs (rerun `sched_hunt.py` with the length pinned at 21 and
  commit the logs) or restated as what reproduces; fix "all 21
  transpositions" (schedules repeat pairs; 20 of 21 *rotations*).
- `.github/workflows/lean-verify.yml`: run on pull requests too; drop the
  no-op first line of the witness step; extend the axiom list.
- Remove `lean/README.md` (Lake template). LICENSE and
  CITATION.cff are the owner's decision (license choice); listed, not made.

## D. Execution order

1. A.0 scaffolding, `lake build`, commit.
2. A layer 1: nine files in parallel (each agent owns one file, checks with
   `lake env lean`, never runs `lake build`); continuation rounds for any
   file left with sorries; then import all, `lake build`, commit.
3. A layer 2 (`Coverage6`), build; A layer 3 (`Faithfulness6`), build;
   axiom check; commit.
4. B.1–B.2 scripts and runs; record results.
5. C, then a consistency pass over every number in the docs; CI; commit;
   open the pull request.

## E. Risks

- `firstApp_relabel` and `shapeClauses_sat` are the two largest lemmas
  (plan risks 2 and 3); budget continuation rounds for them.
- The 720-permutation kernel `decide` for the lower bound may need the
  `permutations'` reformulation and a raised `maxRecDepth`.
- Layer-1 files must not change the layer-0 definitions; any needed
  strengthening is added as a new lemma.
