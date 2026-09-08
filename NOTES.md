# Project notebook (historical)

Chronological working notes moved out of `README.md` on 2026-09-08 when
the repository was prepared for release. Nothing here is needed to
verify the results (see `VERIFYING.md`); it records how the evidence
chains were built, in the order they were built. Later notes:
`f6/CAMPAIGN.md` (the order-6 certificate campaign), `f6/README.md`
(the order-6 attack log), `f7/README.md`, `INSIGHTS.md`.

## Results log (f5, all on Apple M4 Max, single core)

- n=4 sanity: k=10 SAT (0.0s, recount 10), k=11 UNSAT (0.1s) — reproves
  f(4)=10.
- n=5, k=16: SAT in 0.1s; decoded witness independently recounted at
  exactly 16 stable matchings (instance in `f5/paper/f5.tex`).
- n=5, k=17 (with --fix-man0): UNSAT.
  - CaDiCaL 1.9.5 (PySAT), no proof logging: 389.6s.
  - kissat 4.0.4 with proof logging: binary DRAT, 1,093,088,497 bytes.
- Proof verified by drat-trim (backward check, 530.0s): 10,398,816
  lemmas (6,686,848 in core), 462,936,491 resolution steps, 2,490 RAT
  lemmas in core, verdict `s VERIFIED`; LRAT certificate emitted
  (4,327,129,882 bytes).

- RUP-only re-solves (for Mathlib's RUP-only `lrat_proof`):
  - kissat with `--eliminate=false --ands=false --equivalences=false
    --extract=false --substitute=false`: UNSAT, 961MB DRAT, but core still
    had 2,564 RAT lemmas — elimination was not the RAT source.
  - kissat `--plain` (all inprocessing off): UNSAT, 2.12GB DRAT, verified
    in 1276.5s with **0 RAT lemmas in core** — pure-RUP proof achieved;
    Lean import path unblocked. LRAT emission from this proof: see log.

Together: **f(5) = 16, now with a certificate** (three independent
refutations; the plain-mode proof is pure RUP).


## Cube-and-conquer (n=5 Lean import, in progress)

Cubing on man 1's full preference order (120 cubes, orthogonal to the
fix-man0 symmetry): probe of 4 samples showed all UNSAT, pure RUP,
solve 2.9-19.1s each, LRAT 72-428MB per cube. Full 120-cube production
COMPLETE: all 120 cubes UNSAT, pure RUP, each drat-trim-verified; 34GB
total, mean solve 10.5s (`f5/cube_run.py` -> `f5/cubes/`, regenerable,
gitignored). This is a fourth, structurally different refutation of
">=17" (covering split over man 1's preference order).

Architecture B chosen (verified external checker): cake_lpr built
natively for ARM64 from tanyongkiam/cake_lpr (`cake_lpr-src/`, gitignored
build), self-test and n=4 pilot passed, then ALL 120 cube certificates
verified: 120/120 `s VERIFIED UNSAT` (10-way parallel; results in
`f5/cakelpr_results.txt`). Machine side of the f(5)<=16 evidence chain is
complete. Lean math side progress: the covering lemma (cube_covering)
and the ENTIRE symmetry reduction (relabel machinery, isStable_relabel,
stableCount_relabel, reduce_man0') are fully proved, axioms = standard
Mathlib trio only. Sole remaining sorry: f5_upper via the per-cube
encoding-faithfulness bridge.

## Evidence chain status: CLOSED (2026-08-31)

The f(5)=16 proof is complete end-to-end:
1. `f5_upper_of_unsat` (Lean, zero sorries, axioms = propext +
   Classical.choice + Quot.sound): if the 120 Lean-defined cube CNFs are
   unsatisfiable then every well-formed 5x5 instance has <= 16 stable
   matchings. Chain: faithfulness (Faithfulness.lean) + symmetry
   (Symmetry.lean) + covering (Faithful.lean) + assembly (Bridge.lean).
2. The 120 CNFs are printed verbatim from the Lean definitions by
   `export_cnf` (selector encoding; 2,140 vars, 157,197 clauses each);
   a 16-slot positive control was SAT on the witness cube.
3. kissat refuted each cube, drat-trim verified each proof, and the
   formally verified checker cake_lpr certified each LRAT end-to-end:
   **120/120 `s VERIFIED UNSAT`** (`f5/cubesL/cubesL_results.txt`).
4. Lower bound: the 16-matching witness instance is a kernel-only Lean
   theorem (`f5/lean/Witness.lean`, axioms = [propext]).

Outside the Lean kernel, the trust base is: cake_lpr (formally verified),
the 30-line DIMACS printer, and the solver toolchain (whose output is
independently checked, not trusted).

## Independent verification of A344669 (2026-08-31)

Eilers' counts of maximal profiles, previously unreplicated, all confirmed
with our toolchain: a(3)=1092 (full brute force over 46,656 profiles),
a(4)=144 (SAT enumeration: 6 canonical solutions x 4!), and
**a(5)=507,254,400** (incremental-SAT enumeration of all 4,227,120
canonical man0=id solutions across 120 cubes, ~5 min on 8 cores;
`f5/cube_enum.py`, `f5/enum_results.txt`). The quotient 4,227,120/24 =
176,130 also confirms his reduced-instance count in OEIS A357269.

## f(6) = 48 (2026-08-31 .. 09-01; evidence superseded, see the 2026-09-08 entry)

The schedule reduction (see `f6/theory.pdf` and `f6/paper/f6.pdf`):
every instance is dominated in stable-matching count by the read-off
instance of its own rotation schedule, so exhausting the schedule space
(26,574,282,886 nodes, every node's read-off count computed exactly,
~10 h on 8 cores) proves the upper bound; the dihedral instance gives
the lower. Validation: the same machinery reproduces f(3)/f(4)/f(5) =
3/10/16 (the last certified by this repo's own Lean theorem),
canonicalization on/off agrees at 4.5x/14x/48x tree blowups, and an
independent Python implementation agrees throughout.

**Lean formalization of the reduction (complete, 2026-09-01):**
`f5/lean/SmpF5/SmpF5/{SixBridge,Lattice6,Chain6}.lean` — 1,849 lines,
105 theorems, zero sorries, axioms = the standard trio. Highlights:
`bridge` (sc(I) <= sc(readoff I)), `chain_complete` (a maximal cover
chain from man-optimal to woman-optimal realizes every stable pair),
the trajectory budget theorems (`traj_*`, `wtraj_*`,
`total_moves_le_30`), and the step cycle-structure lemmas
(`prevOwner_*`). The only unformalized link is a verified replay of the
enumeration itself. *(2026-09-08: no longer the plan; the enumeration
is corroboration and the certificate campaign is the evidence - next
entry.)*

## f(6) = 48: certificate campaign complete, audited, Lean identity checks closed (2026-09-08)

The order-6 upper bound now rests on the certificate campaign
(`f6/CAMPAIGN.md`), not on the enumeration above. The Lean-defined
formula `SchedCNF6` ("some legal schedule reads off >= 49") was refuted
cube by cube: 25,493 root cubes; 321,492 distinct cubes in the split
tree (depth 0: 1; depth 1: 153; depth 2: 27,143 = 25,339 open roots +
1,804 stop-children of the depth-2 splits; depth 3: 197,814; depth 4:
96,381); 318,736 cake_lpr-verified (1 / 153 / 25,339 / 196,862 / 96,381
by depth); 2,756 split (1,804 at depth 2, 952 at depth 3); 2,910 closed
(stop) cubes; 0 SAT. One solver build throughout: CaDiCaL 3.0.1
c6073042 (`--lrat --binary=false`); solver time 1,076,400 s, median
1.0 s per cube; certificates summed to about 25 TB and were deleted
after checking. `python3 f6/cube_campaign.py --audit` exits 0
(roots=25493 nodes=321492 verified=318736 missing=0 bad=0
header_problems=0). Provenance (last record per cube): Linux/x86-64
container 3,967 verified + 235 split (x86-64 cake_lpr build, cake_lpr.S
sha256 2f3af32d...); Apple M4 Max laptop 12,727 + 628; Mac mini M4 Pro
302,042 + 1,893 (arm64 build, cake_lpr_arm8.S sha256 95b64883...). The
released journal (`f6/campaign/campaign.jsonl.gz`, 40,943,262 bytes,
sha256 c9026b08045d8e8824c66d213bfa8eeb5336f118c22e030d42040136be7a8e4e)
is one append lineage laptop -> container -> Mac mini; the parallel
three-worker laptop snapshot of commit 8256eef never entered it.

Lean identity checks, all passed (`f6/campaign/lean_identity.txt`):
base formula byte-identical (sha256 28421fb6...); the 25,493 root cubes
byte-identical; the 295,999 split children byte-identical; the
Lean-defined certified cube set `finalCubes` (`SplitList6.lean`:
`refineCubes` of `canonicalCubes2` by the 1,804 + 952 recorded split
ids) equals the 318,736 verified ids as a set; all 321,492 journaled
`cnf_sha256` values recompute from the Lean-printed header, body and
unit clauses (`f6/lean_rehash.py`, exit 0).

Trust statement: the journal is self-attested - a "verified" record is
the driver's transcription of cake_lpr's verdict, and the certificates
are gone. Independent verification of a verdict means re-solving that
cube from the Lean-printed formula; the per-cube `cnf_sha256` /
`lrat_sha256` let a re-run be compared record by record (about 300
core-hours for the whole tree). The enumeration (`gen_enum.c`,
26,574,282,886 schedules, max 48) is corroboration. Still not a Lean
theorem: faithfulness - every well-formed order-6 instance with >= 49
stable matchings satisfies some certified cube's formula; see
`STATUS.md` for its status.
