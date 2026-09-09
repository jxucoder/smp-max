# Status: what is established, by what evidence, and what is next

Last updated 2026-09-09 (paths updated for the repository layout change,
see the last line of "Numbers behind the ledger"). This is the evidence
ledger of the project: for each claim, the kind of evidence behind it, the
cross-checks that guard against systematic error, and the ordered list of
what remains. It is meant to be updated whenever a claim changes. It is
also the single home of the campaign numbers; other documents point here
rather than repeating them.

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
  checker (see "What remains outside the kernel" under f(6) = 48).
- **Validated computation.** A program whose output agrees with
  independent programs and known values but has not itself been proved
  correct.

## Claims

Each claim below uses the same template: theorem, hypothesis,
certificates, identity checks, corroboration, and what remains outside
the kernel. The two headline claims have the same shape: one Lean theorem
over the definitions at the top of `Faithful.lean` (order 5) and
`SixBridge.lean` (order 6), whose single hypothesis is discharged by
cake_lpr-checked certificates for formulas printed from the Lean
definitions. All Lean files are under `lean/SmpMax/` unless noted.

### f(5) = 16

- **Theorem.** `f5_eq_16_of_unsat` (`lean/SmpMax/Five/ExactMaximum.lean`):
  `(∀ row ∈ perms120, ¬Satisfiable (cubeCNF row)) → (∀ I : Inst, WF I = true → stableCount I ≤ 16) ∧ ∃ I, WF I = true ∧ stableCount I = 16`.
  Zero sorries; axioms `propext`, `Classical.choice`, `Quot.sound`. The
  witness is a kernel-only theorem (`lean/checks/FiveWitness.lean`, axiom `propext`
  only).
- **Hypothesis.** The 120 Lean-defined cube formulas `cubeCNF row`,
  `row ∈ perms120`, are unsatisfiable.
- **Certificates.** 120 of 120 cubes, cake_lpr `s VERIFIED UNSAT`
  (`results/f5/lean-cubes/verification.txt`).
- **Identity checks.** The cube formulas are printed from the Lean
  definitions by `lean/ExportFiveCnf.lean`; `docs/verification.md` regenerates
  and re-checks them.
- **Corroboration.** None needed; the whole chain is kernel-checked
  theorem plus checked certificates. (Earlier, independent refutations by
  the direct encoding are recorded in `docs/history/research-notebook.md`.)
- **What remains outside the kernel.** The trust base of `docs/verification.md`:
  the Lean kernel and its three axioms, the definitions at the top of
  `Faithful.lean`, one LRAT checker, and the DIMACS printer.

### f(6) = 48 (upper bound; the theorem also carries the lower bound)

- **Theorem.** `f6_eq_48_of_unsat` (`lean/SmpMax/Six/ExactMaximum.lean`):
  `(∀ c ∈ Cubes6.finalCubes, ¬Satisfiable (Cubes6.cubeFormula 49 c)) → (∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48) ∧ ∃ I, WF6 I = true ∧ stableCount6 I = 48`.
  Zero sorries; axioms `propext`, `Classical.choice`, `Quot.sound`. Inside
  the kernel it composes the reduction (`validity_unconditional` and the
  rest of the 11-file reduction layer, 5,231 lines, 243 theorems), the
  faithfulness layer (`exists_canonical_schedule`, `fits_final`,
  `cube_faithful6`; 19 files, 4,761 lines, 333 theorems, plus the
  2,808-line data file `lean/SmpMax/Six/CampaignSplits.lean` holding the 2,756 recorded split
  decisions that define `finalCubes`) and the witness `dihedral6_count`
  (below).
- **Hypothesis.** The 318,736 cube formulas `cubeFormula 49 c`,
  `c ∈ Cubes6.finalCubes`, are unsatisfiable. `finalCubes` is a Lean
  definition (`Cubes6.lean`, `lean/SmpMax/Six/CampaignSplits.lean`): the leaves of the split
  tree over the 25,493 root cubes of `SchedCNF6.schedCNF49`.
- **Certificates.** All 318,736 leaves: cake_lpr `s VERIFIED UNSAT`,
  0 SAT, `cube_campaign.py --audit` exit 0 (`results/f6/campaign-2026-09-08/audit-complete.txt`;
  provenance and toolchain in `docs/reference/campaign.md`). Journal:
  `results/f6/campaign-2026-09-08/campaign.jsonl.gz`, sha256
  `c9026b08045d8e8824c66d213bfa8eeb5336f118c22e030d42040136be7a8e4e`.
- **Identity checks.** Re-checked for every cube
  (`results/f6/campaign-2026-09-08/lean_identity.txt`): base formula byte-identical to the
  Python writer's; the 25,493 root cubes and all 295,999 split children
  byte-identical; `finalCubes` = the journal's verified set; all 321,492
  journaled formula hashes recomputed from Lean-printed pieces
  (`tools/campaign/verify_lean_hashes.py`). Details in "What guards the f(6) certificate
  layer" below.
- **Corroboration** (validated computation only). The exhaustive
  enumeration of all 26,574,282,886 schedules, maximum 48
  (`experiments/enumeration/enumerate_cycle_schedules.c`); hill-climbing over instances and over
  schedules ([enumeration experiments](../experiments/README.md)). Corroboration, not evidence.
- **What remains outside the kernel.** Item for item the f(5) trust base
  (`docs/verification.md`): the Lean kernel and its three axioms; the definitions
  `Inst6`, `WF6`, `isStable6`, `sms6`, `stableCount6` (about 40 lines at
  the top of `SixBridge.lean`, the one human-checked step); one LRAT
  checker; the printers `lean/ExportSixCnf.lean` and
  `lean/ExportSixCubes.lean` together with the file identity above;
  and the campaign journal. The journal is self-attested: a `verified`
  record is the driver's transcription of cake_lpr's verdict, the
  certificates (about 25 TB) were deleted after checking, and the audit
  checks the records' consistency. Independently verifying a verdict
  means re-solving that cube from the Lean-printed formula (the per-cube
  `cnf_sha256` and `lrat_sha256` make a re-run comparable record by
  record); the whole tree is about 300 core-hours of solver time; a
  205-cube sample has been re-solved independently ("Independent checks"
  below). Lean's `leanchecker` has been run over every module (below).
  Not trusted: solvers, Python scripts, `gen_enum.c`, the plan documents
  (`docs/history/`).

### f(6) ≥ 48

- **Theorem.** `dihedral6_count : stableCount6 dihedral6 = 48`
  (`lean/SmpMax/Six/LowerBound.lean`): the dihedral instance has exactly 48
  stable matchings, by kernel computation (`decide`) over the 720
  permutations. It is the witness half of `f6_eq_48_of_unsat`.
- **Hypothesis.** None.
- **Certificates.** None needed.
- **Identity checks.** The instance is a Lean literal (`dihedral6`); its
  ranking matrix is displayed in `docs/f6.md`.
- **Corroboration.** The same instance recounted at 48 by three
  independent programs (`tools/stable_matchings.py`, `tools/rotation_poset.py`,
  `sched_sat.readoff_counts` in `tools/schedule_encoding.py`).
- **What remains outside the kernel.** Nothing beyond the kernel, the
  three axioms and the definitions at the top of `SixBridge.lean`.

### f(7) ≥ 85

- **Theorem.** None; this is a validated computation, not a proof object.
- **Hypothesis.** —
- **Certificates.** —
- **Identity checks.** The two instances are re-derived byte-identically
  from their schedules (`python3 experiments/search/search_swap_schedules.py 7 <seed> <seconds>`,
  re-done 2026-09-08).
- **Corroboration.** Two explicit instances (`results/f7/witnesses-85.txt`), each counted
  at 85 by brute force, by an explicit all-blocking-pairs recount, and via
  the rotation poset's downsets; the search runs behind the claims are
  logged in `results/f7/search/`. Previous published bound: 81 (`docs/f7.md`).
- **What remains outside the kernel.** Everything: three unproved
  counting programs agreeing with each other.

### A344669(3,4,5) = 1092 / 144 / 507,254,400

- **Theorem.** None.
- **Hypothesis.** —
- **Certificates.** —
- **Identity checks.** —
- **Corroboration.** Independent recount: brute force over all 46,656
  profiles for n = 3, SAT enumeration for n = 4 and n = 5
  (`experiments/enumeration/enumerate_f5_profiles.py`; the n = 5 per-cube counts in `results/f5/profile-enumeration.txt`,
  the n = 3 and n = 4 confirmations recorded in `docs/history/research-notebook.md`),
  confirming Eilers'
  unreplicated counts. The OEIS comment text is in `docs/oeis-draft.md`.
- **What remains outside the kernel.** Everything: a validated
  computation agreeing with one prior computation.

## What guards the f(6) certificate layer against systematic error

1. **Single source of truth for the formula and the cubes.** The CNF is
   defined in Lean (`lean/SmpMax/Six/ScheduleEncoding.lean`, a line-by-line
   transcription of `tools/schedule_encoding.py`) and printed by `export_sched_cnf`
   (`lean/ExportSixCnf.lean`); the root cubes, the split children
   and the certified cube set `finalCubes` are Lean definitions
   (`Cubes6.lean`, `lean/SmpMax/Six/CampaignSplits.lean`) printed by `export_cubes6`
   (`lean/ExportSixCubes.lean`). The theorem quantifies over these
   definitions, not over any Python object.
2. **Every formula re-derived.** The Lean output is byte-identical to the
   Python writer's for the base formula (sha256 `28421fb6…`, 84,882
   variables, 2,709,212 clauses), and all 321,492 journaled `cnf_sha256`
   values (hashed by the driver before solving) recompute from the
   Lean-printed header, base body and unit clauses (`tools/campaign/verify_lean_hashes.py`,
   `matched=321492 mismatched=0`; transcript `results/f6/campaign-2026-09-08/lean_identity.txt`).
3. **Cube-set identity.** `canonicalCubes2` prints the driver's 25,493
   root ids byte-identically; `extendCanon` prints the 295,999 children of
   all 2,756 journaled splits byte-identically; `finalCubes` prints
   exactly the 318,736 `verified` ids.
4. **The audit.** `tools/campaign/cube_campaign.py --audit` recomputes the root set,
   checks that every root is `verified` or `split` with all children
   recursively covered, and checks every verified record's fields: solver
   rc 20, the driver-derived `cake_verified` boolean (defined at write
   time as `s VERIFIED UNSAT` in cake_lpr's output and not killed) with
   `cake_rc 0`, no kill flag, well-formed hashes. Final verdict:
   `roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0`
   (`results/f6/campaign-2026-09-08/audit-complete.txt`; the earlier main-run audit is
   `results/f6/campaign-2026-09-08/audit-before-retries.txt`). It is a consistency check of the
   journal, not a re-check of any certificate.
5. **Positive control (encoding not vacuous).** With the dihedral
   schedule pinned
   (`--prefix` `0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5`),
   the formula at k = 48 is satisfiable; the model decodes to exactly that
   schedule with 48 distinct selected matchings and an independent recount
   of the read-off gives 48; the same cube at k = 49 is unsatisfiable
   (re-run 2026-09-08 with pysat/CaDiCaL).
6. **Agreement across unrelated methods.** The certificate campaign,
   the direct enumeration of the schedule space
   (`experiments/enumeration/enumerate_cycle_schedules.c`), and hill-climbing over instances and
   over schedules (> 10^9 evaluations; `experiments/search/search_instances.py`,
   `struct_hunt.py`, `relaxed_search.py`) all top out at 48; the same
   machinery reproduces f(3), f(4), f(5) = 3, 10, 16, the last against
   this repository's own certified theorem.

The driver's pilot runs (dry run, fix check, depth-3 probe, CaDiCaL
checks) are in `results/f6/campaign-2026-09-08/` (the named probe files); the scripts that ran and monitored
the campaign are in `docs/history/container-scripts/` (archived shell scripts) and `tools/campaign/` (maintained tools). Neither directory is on the
evidence path.

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
   effect). `results/f6/campaign-2026-09-08/recheck_2026-09-09.txt` and the new journal
   `results/f6/campaign-2026-09-08/recheck_2026-09-09.jsonl` record commands, hashes and
   times (263 s wall for the sample). This confirms the journal's
   self-report on the sample; it does not replace re-solving the other
   318,531 cubes. The recipe (`cube_campaign.py --solver cadical --force
   ... --cubes <ids>`, then compare `cnf_sha256` / `lrat_sha256` per cube
   with the journal's last record for that cube) is the "Reproduce" block
   of `results/f6/campaign-2026-09-08/recheck_2026-09-09.txt`, also given in `docs/verification.md`.
2. **`leanchecker` over the development.** Lean 4.33.1's built-in
   `leanchecker` replayed every declaration of all 37 imported modules and
   the root module through the kernel on 2026-09-09: 38 / 38 clean (silent
   exit 0), about 8 s per module; a nonexistent module name errors, so the
   tool was live (`results/f6/campaign-2026-09-08/leanchecker_2026-09-09.txt`).

## Remaining work

The [roadmap](roadmap.md) lists publication, third-party re-checking and
larger-order research. [Publishing instructions](publishing.md) retain the
draft release state. No license is selected for this checkout.

## Numbers behind the ledger

| item | value |
|---|---|
| order-6 campaign, distinct cubes | 321,492 (roots 25,493 = 1 + 153 + 25,339; by depth 0/1/2/3/4: 1 / 153 / 27,143 / 197,814 / 96,381; closed `stop` cubes 2,910) |
| verified certificates | 318,736 (by depth 1 / 153 / 25,339 / 196,862 / 96,381) |
| splits | 2,756 (1,804 at depth 2, rate 7.1%; 952 at depth 3, rate 0.48%; reasons: LRAT-size watchdog 2,692, solver killed 11, check timeout 13, none recorded 40) |
| SAT records | 0 |
| total solver time | 1,076,400 s (median 1.0 s per cube) |
| certificate sizes | median 35 MB, max 9.8 GB; about 25 TB checked and deleted |
| base formula | `SchedCNF6.schedCNF49`: 84,882 variables, 2,709,212 clauses, sha256 `28421fb6…`; Lean print byte-identical to `tools/schedule_encoding.py` |
| provenance (last record per cube) | Linux/x86-64 container 3,967 verified + 235 split (x86-64 cake_lpr, `cake_lpr.S` sha256 `2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a`); Apple M4 Max 12,727 + 628; Mac mini M4 Pro 302,042 + 1,893 (arm64, `cake_lpr_arm8.S` sha256 `95b64883edc0cb09feedbcb1ebec233e2490f5b458fdda9dc29c212ed916f00c`) |
| toolchain | CaDiCaL 3.0.1, commit `c60730422e758ef1cebe7aeddf2dda31c996bf04` (`--lrat --binary=false`), one build per machine; cake_lpr from tanyongkiam/cake_lpr @ `a36874a` in the two builds above (self-test: `cake_lpr example.cnf example.lpr` → `s VERIFIED UNSAT`); kissat 4.0.4 + drat-trim for f(5) only |
| journal | `results/f6/campaign-2026-09-08/campaign.jsonl.gz`, 40,943,262 bytes, sha256 `c9026b08045d8e8824c66d213bfa8eeb5336f118c22e030d42040136be7a8e4e`; 321,701 records, last record per cube wins |
| Lean identity checks | base formula, 25,493 roots, 295,999 split children: byte-identical; `finalCubes` = verified set; 321,492 / 321,492 formula hashes recomputed (`results/f6/campaign-2026-09-08/lean_identity.txt`) |
| Lean, order-6 reduction layer | 11 files, 5,231 lines (5,230 when the papers were written; one docstring line since), 243 theorems, zero sorries |
| Lean, order-6 faithfulness layer | 19 files, 4,761 lines, 333 theorems, zero sorries; plus `lean/SmpMax/Six/CampaignSplits.lean`, 2,808 lines of data |
| Lean, whole development | 37 imported modules, 13,937 lines, 646 theorems (order-5 core: 6 files, 1,137 lines, 70 theorems; reduction 11 / 5,231 / 243; faithfulness 19 / 4,761 / 333; `lean/SmpMax/Six/CampaignSplits.lean` 2,808 lines of data; counted with `grep -cE '^theorem|^lemma'`); original `lake build` 893 jobs (job counts vary with targets); `grep -rn sorry lean/SmpMax/` empty; Lean 4.33.1 + Mathlib |
| CI | `lean-verify` on pushes to `main`, pull requests and dispatch: build, no-sorry grep, axiom checks on 1 + 25 theorems (`.github/workflows/lean-verify.yml`); `build-papers` compiles the three papers |
| independent re-solve sample (2026-09-09) | 205 cubes, second machine, pinned toolchain rebuilt from source: 205 verified, 205 / 205 formula hashes equal, 204 / 205 certificate hashes equal (198 / 198 same-architecture) |
| `leanchecker` (2026-09-09) | 38 / 38 modules replayed through the kernel, 0 failures (Lean 4.33.1, arm64) |
| direct enumeration (corroboration) | 26,574,282,886 schedules, maximum 48 (`experiments/enumeration/enumerate_cycle_schedules.c`; rebuild with `cc -O2 -o gen_enum_c experiments/enumeration/enumerate_cycle_schedules.c`; shard logs in `results/f6/enumeration/maximal-node-logs.tar.gz`, `results/f6/enumeration/all-node-logs.tar.gz`) |
| repository layout | The 2026-09-09 cleanup uses `lean/SmpMax/Five/` and `lean/SmpMax/Six/`, reusable `tools/`, `experiments/`, `results/`, and `papers/`. See the [migration map](path-migration.md) and [validation](layout-verification.md). Historical transcripts retain original paths. |
