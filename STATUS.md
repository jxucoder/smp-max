# Status: what is established, by what evidence, and what is next

Last updated 2026-09-09. This is the evidence ledger of the
project: for each claim, the kind of evidence behind it, the cross-checks
that guard against systematic error, and the ordered list of what remains.
It is meant to be updated whenever a row changes.

## Three kinds of evidence

The repository uses three kinds of evidence, and they are not
interchangeable:

- **Kernel-checked theorem.** A statement verified by the Lean 4 kernel
  from the definitions, resting only on the axioms `propext`,
  `Classical.choice`, `Quot.sound`. Anyone can re-run the check
  (`lake build`, `#print axioms`).
- **Checked certificate.** A proof of unsatisfiability of a specific
  DIMACS formula, verified by cake_lpr, a checker whose own correctness
  is proved down to machine code. The solver that produced it is not
  trusted; only the checker's verdict is. For the order-6 campaign the
  verdicts are recorded in a journal written by the driver that ran the
  checker (see "What remains outside the kernel").
- **Validated computation.** A program whose output agrees with
  independent programs and known values but has not itself been proved
  correct.

## The ledger

| claim | kernel-checked theorem | checked certificates | validated computation only |
|---|---|---|---|
| **f(5) = 16** | the whole chain: `f5_eq_16_of_unsat` (`f5/lean/SmpF5/SmpF5/Lower.lean`), whose only hypothesis is "these 120 Lean-defined cube formulas are unsatisfiable"; the witness is a kernel-only theorem (`Witness.lean`, axiom `propext` only) | 120 of 120 cubes, cake_lpr `s VERIFIED UNSAT` (`f5/cubesL/cubesL_results.txt`) | none |
| **f(6) = 48** | the whole chain: `f6_eq_48_of_unsat` (`f5/lean/SmpF5/SmpF5/Bridge6.lean`), whose only hypothesis is "the 318,736 cube formulas of `Cubes6.finalCubes` are unsatisfiable". It composes the reduction (`validity_unconditional` and the rest of the 11-file reduction layer, 5,230 lines, 243 theorems), the faithfulness layer (`exists_canonical_schedule`, `fits_final`, `cube_faithful6`; 19 files, 4,761 lines, 333 theorems, plus the 2,808-line data file `SplitList6.lean` holding the 2,756 recorded split decisions that define `finalCubes`) and the witness `dihedral6_count : stableCount6 dihedral6 = 48` (`Lower6.lean`, kernel `decide`). Zero sorries, standard axioms | all 318,736 leaves of the split tree over the 25,493 root cubes of `SchedCNF6.schedCNF49`: cake_lpr `s VERIFIED UNSAT`, 0 SAT, `cube_campaign.py --audit` exit 0 (`f6/campaign/audit_final.txt`, `f6/CAMPAIGN.md`). Identity with the Lean statement re-checked for every cube: base formula byte-identical, root cubes and all 295,999 split children byte-identical, `finalCubes` = the verified set, and all 321,492 journaled formula hashes recomputed from Lean-printed pieces (`f6/campaign/lean_identity.txt`) | the exhaustive enumeration of all 26,574,282,886 schedules, maximum 48 (`f6/gen_enum.c`), as corroboration only |
| **f(6) ≥ 48** | `dihedral6_count` (`Lower6.lean`): the dihedral instance has exactly 48 stable matchings, by kernel computation over the 720 permutations | — | the same instance recounted at 48 by three independent programs (`smp.py`, `rotation_poset.py`, `sched_sat.readoff_counts`) |
| **f(7) ≥ 85** | — | — | two explicit instances (`f7/lb85.txt`), each counted at 85 by brute force, by an explicit all-blocking-pairs recount, and via the rotation poset's downsets; re-derived from their schedules on 2026-09-08; the search runs behind the claims are logged in `f7/logs/` |
| **A344669(3,4,5) = 1092 / 144 / 507,254,400** | — | — | independent SAT enumeration (`f5/cube_enum.py`; the n = 5 per-cube counts in `f5/enum_results.txt`, the n = 3 and n = 4 confirmations recorded in `NOTES.md`), confirming Eilers' unreplicated counts |

The two headline rows now have the same shape: one Lean theorem over the
definitions at the top of `Faithful.lean` (order 5) and `SixBridge.lean`
(order 6), whose single hypothesis is discharged by cake_lpr-checked
certificates for formulas printed from the Lean definitions.

## What guards the f(6) certificate layer against systematic error

1. **Single source of truth for the formula and the cubes.** The CNF is
   defined in Lean (`SchedCNF6.lean`, a line-by-line transcription of
   `f6/sched_sat.py`) and printed by `export_sched_cnf`; the root cubes,
   the split children and the certified cube set `finalCubes` are Lean
   definitions (`Cubes6.lean`, `SplitList6.lean`) printed by
   `export_cubes6`. The theorem quantifies over these definitions, not
   over any Python object.
2. **Every formula re-derived.** The Lean output is byte-identical to the
   Python writer's for the base formula (sha256 `28421fb6…`, 84,882
   variables, 2,709,212 clauses), and all 321,492 journaled `cnf_sha256`
   values (hashed by the driver before solving) recompute from the
   Lean-printed header, base body and unit clauses (`f6/lean_rehash.py`,
   `matched=321492 mismatched=0`).
3. **Cube-set identity.** `canonicalCubes2` prints the driver's 25,493
   root ids byte-identically; `extendCanon` prints the 295,999 children of
   all 2,756 journaled splits byte-identically; `finalCubes` prints
   exactly the 318,736 `verified` ids.
4. **The audit.** `cube_campaign.py --audit` recomputes the root set,
   checks that every root is `verified` or `split` with all children
   recursively covered, and checks every verified record's fields: solver
   rc 20, the driver-derived `cake_verified` boolean (defined at write
   time as `s VERIFIED UNSAT` in cake_lpr's output and not killed) with
   `cake_rc 0`, no kill flag, well-formed hashes. Final verdict:
   `roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0`.
   It is a consistency check of the journal, not a re-check of any
   certificate.
5. **Positive control (encoding not vacuous).** With the dihedral
   schedule pinned, the formula at k = 48 is satisfiable; the model
   decodes to exactly that schedule with 48 distinct selected matchings
   and an independent recount of the read-off gives 48; the same cube at
   k = 49 is unsatisfiable (re-run 2026-09-08 with pysat/CaDiCaL).
6. **Agreement across unrelated methods.** The certificate campaign,
   the direct enumeration of the schedule space, and hill-climbing over
   instances and over schedules (> 10^9 evaluations) all top out at 48;
   the same machinery reproduces f(3), f(4), f(5) = 3, 10, 16, the last
   against this repository's own certified theorem.

## What remains outside the kernel

Item for item the f(5) trust base (`VERIFYING.md`): the Lean kernel and
its three axioms; the definitions `Inst6`, `WF6`, `isStable6`, `sms6`,
`stableCount6` (about 40 lines at the top of `SixBridge.lean`, the one
human-checked step); one LRAT checker; the printers `ExportSchedCnf.lean`
and `ExportCubes6.lean` together with the file identity above; and the
campaign journal. The journal is self-attested: a `verified` record is the
driver's transcription of cake_lpr's verdict, the certificates (about
25 TB) were deleted after checking, and the audit checks the records'
consistency. Independently verifying a verdict means re-solving that cube
from the Lean-printed formula (the per-cube `cnf_sha256` and
`lrat_sha256` make a re-run comparable record by record); the whole tree
is about 300 core-hours of solver time; a 205-cube sample has been
re-solved independently (below). Lean's `leanchecker` has been run over
every module (below). Not trusted: solvers, Python scripts, `gen_enum.c`,
the plan documents.

## Independent checks (2026-09-09)

1. **Re-solve of a random cube sample with the pinned toolchain, on a
   second machine.** 205 verified cubes (stratified by depth and
   closedness; 164 originally solved on the Mac mini, 34 on the M4 Max
   laptop, 7 on the x86-64 container) were re-solved on another Mac from a
   fresh clone, with CaDiCaL rebuilt at commit `c6073042` and cake_lpr
   built from the hash-checked `cake_lpr_arm8.S` (`95b64883…`): 205 / 205
   verified (`s VERIFIED UNSAT`), 205 / 205 `cnf_sha256` equal to the
   journal, 204 / 205 `lrat_sha256` equal (all 198 arm64-origin records
   byte-identical; one of the 7 container-origin records has a different
   proof trace of the same formula, same verdict, an architecture/compiler
   effect). `f6/campaign/recheck_2026-09-09.txt` and the new journal
   `recheck_2026-09-09.jsonl` record commands, hashes and times (263 s wall
   for the sample). This confirms the journal's self-report on the sample;
   it does not replace re-solving the other 318,531 cubes.
2. **`leanchecker` over the development.** Lean 4.33.1's built-in `leanchecker` replayed every
   declaration of all 37 imported modules and the root module through the
   kernel on 2026-09-09: 38 / 38 clean (silent exit 0), about 8 s per
   module; a nonexistent module name errors, so the tool was live
   (`f6/campaign/leanchecker_2026-09-09.txt`).

## What is next, in order

1. **Publish the evidence** (`PUBLISHING.md`). Done: LICENSE
   (Apache-2.0), `CITATION.cff`, `.zenodo.json`, the PDFs rebuilt from the
   current sources, a GitHub release. Needs the owner's accounts: the
   Zenodo DOI (enable the GitHub integration, then the release is
   archived; the journal's sha256 is
   `c9026b08045d8e8824c66d213bfa8eeb5336f118c22e030d42040136be7a8e4e`),
   arXiv for both papers, OEIS A357269 a(6) = 48 and the comments on
   A357271 / A344669 (`f6/OEIS_DRAFT.md`).
2. **A third-party re-check** by someone other than the author: the
   sample re-solve above is reproducible from the Lean-printed formulas
   (`f6/campaign/recheck_2026-09-09.txt`); the whole tree is about 300
   core-hours.
3. **Lower bounds at odd orders 9 to 15** with the schedule search of
   `f7/` (needs an O(n^2) rotation extractor to count through the
   rotation poset); the published bounds there look as soft as 81 did.
4. **Conjecture 1** (extremal instances come from all-size-2 schedules,
   full-budget at even orders), which the order-7 data support.

## Numbers behind the ledger

| item | value |
|---|---|
| order-6 campaign, distinct cubes | 321,492 (roots 25,493 = 1 + 153 + 25,339; by depth 0/1/2/3/4: 1 / 153 / 27,143 / 197,814 / 96,381; closed `stop` cubes 2,910) |
| verified certificates | 318,736 (by depth 1 / 153 / 25,339 / 196,862 / 96,381) |
| splits | 2,756 (1,804 at depth 2, rate 7.1%; 952 at depth 3, rate 0.48%; reasons: LRAT-size watchdog 2,692, solver killed 11, check timeout 13, none recorded 40) |
| SAT records | 0 |
| total solver time | 1,076,400 s (median 1.0 s per cube) |
| certificate sizes | median 35 MB, max 9.8 GB; about 25 TB checked and deleted |
| provenance (last record per cube) | Linux/x86-64 container 3,967 verified + 235 split (x86-64 cake_lpr, `cake_lpr.S` `2f3af32d…`); Apple M4 Max 12,727 + 628; Mac mini M4 Pro 302,042 + 1,893 (arm64, `cake_lpr_arm8.S` `95b64883…`) |
| toolchain | CaDiCaL 3.0.1 `c6073042` (`--lrat --binary=false`), one build per machine; cake_lpr in the two builds above |
| journal | `f6/campaign/campaign.jsonl.gz`, 40,943,262 bytes, sha256 `c9026b08…`; 321,701 records, last record per cube wins |
| Lean identity checks | base formula, 25,493 roots, 295,999 split children: byte-identical; `finalCubes` = verified set; 321,492 / 321,492 formula hashes recomputed |
| Lean, order-6 reduction layer | 11 files, 5,230 lines, 243 theorems, zero sorries |
| Lean, order-6 faithfulness layer | 19 files, 4,761 lines, 333 theorems, zero sorries; plus `SplitList6.lean`, 2,808 lines of data |
| Lean, whole development | 37 imported modules, 15,785 lines, 647 theorems; `lake build` 893 jobs |
| CI | `lean-verify` on pushes to `main`, pull requests and dispatch: build, no-sorry grep, axiom checks on 1 + 25 theorems (`.github/workflows/lean-verify.yml`); `build-papers` compiles the three papers |
| independent re-solve sample (2026-09-09) | 205 cubes, second machine, pinned toolchain rebuilt from source: 205 verified, 205 / 205 formula hashes equal, 204 / 205 certificate hashes equal (198 / 198 same-architecture) |
| `leanchecker` (2026-09-09) | 38 / 38 modules replayed through the kernel, 0 failures (Lean 4.33.1, arm64) |
