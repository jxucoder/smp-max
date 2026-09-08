# smp-max: certified maximum numbers of stable matchings

Machine-checkable proofs for f(n) = max number of stable matchings of an
n x n stable-marriage instance (Knuth 1976, Research Problem #5;
Gusfield-Irving 1989, Open Problem #1).

- **[f5/](f5/)** — DONE: first machine-checkable proof of f(5)=16.
  Single Lean theorem `f5_eq_16_of_unsat` (zero sorries, standard
  axioms), 120 Lean-defined CNFs refuted with certificates checked by
  the formally verified cake_lpr, 120/120. Paper: `f5/paper/f5.pdf`.
- **[f6/](f6/)** — RESOLVED: f(6)=48 (previously open, conjectured in
  OEIS A357271). Schedule reduction + exhaustive evaluation of all
  26,574,282,886 schedule read-off instances; the reduction lemmas
  (bridge + validity) are formalized in Lean with zero sorries. Paper:
  `f6/paper/f6.pdf`; theory notes: `f6/theory.pdf`. **Certificate
  campaign complete (2026-09-08):** the schedule-space formula was
  refuted cube by cube, 318,736 cake_lpr-checked UNSAT certificates over
  25,493 root cubes and their splits, 0 SAT, `--audit` exit 0
  (`f6/CAMPAIGN.md` "Result"). The Lean faithfulness proof tying the
  formula to `stableCount6` is in progress (`f6/FAITHFULNESS_PLAN.md`).

**Status: PRIVATE.** Not yet published; OEIS not yet notified. See
`INSIGHTS.md` for the retrospective and the publication checklist.

## Layout

- `smp.py` — brute-force stable-matching counter. Validated against the
  OEIS A351413 extremal Latin instances (n=3,4,5,6 → 3/10/9/48).
- `encode.py` — SAT encoding of "exists an n x n instance with >= k stable
  matchings": pairwise-preference variables + transitivity (no-3-cycle),
  one indicator per perfect matching with S → stability clauses (one
  direction suffices), sequential-counter cardinality. `--fix-man0` pins
  man 0's list to identity (sound by woman-relabeling). `--dimacs` exports
  CNF for external solvers.
- `f5/` — CNF, run logs, paper draft. Proof artifacts (1.0GB DRAT / 4.0GB
  LRAT and their zstd compressions, 294MB / 825MB) are gitignored for
  now; they will be attached to a release or archived on Zenodo.
- `f6/` — known instance, why n=6 is harder, attack plan.

External tool: [drat-trim](https://github.com/marijnheule/drat-trim)
(clone into `dt-src/`, gitignored).

## State of the art (due diligence, 2026-08)

- f(1..5) = 1, 2, 3, 10, 16 — OEIS [A357269](https://oeis.org/A357269).
- f(5)=16: announced by Dan Eilers (Sep 2022, MiniZinc); his paper is
  still "in preparation", and no proof object of any kind existed before
  this project.
- f(6): was open with best lower bound 48 (dihedral Latin instance,
  [A351413](https://oeis.org/A351413)), conjectured exact
  ([A357271](https://oeis.org/A357271)) — **resolved here: f(6)=48**.
- f(7): open. [A357271](https://oeis.org/A357271) tabulates Thurber's
  2002 composition bounds (a(7)=71), but its linked
  [Ong et al. 2024 file](https://oeis.org/A357271/a357271_1.txt)
  (Ong, Ang, Ho, Eilers, Marks, Buzi, IFoRE 2024) improves every ODD
  order by hill climbing: lb(7)=81, lb(9)=365, lb(11)=1690,
  lb(13)=7123, lb(15)=27059. Even orders are unimproved, so f(6)=48
  remains the best lower bound at 6 and this repo's result stands.
  **Improved here: f(7) >= 85** (`f7/`, checked 2026-09-06 against the
  OEIS entry as last edited May 2025).
- General bounds: 2.28^n <= f(n) (Thurber 2002), f(n) <= 3.55^n
  (Palmer-Pálvölgyi), first exponential bound Karlin-Oveis Gharan-Weber
  STOC 2018.

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

## f(6) = 48 (2026-08-31 .. 09-01)

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
enumeration itself.

## Next steps

1. (When owner says go) publication sequence: see `INSIGHTS.md`
   checklist — repo public, Zenodo DOI, arXiv both papers, OEIS.
2. Verified replay / certified reimplementation of the f(6)
   enumeration — architectures + pilot plan in `f6/REPLAY_DESIGN.md`.
3. The general-n conjecture (all-size-2 schedules; full budget at even
   orders) — stated as Conjecture 1 in `f6/paper/f6.pdf`.
4. f(7): lower bounds are the live opportunity — see `f7/`, which
   already improves the best known from 81 to 85. The upper bound is
   not: the certified cube route is 3-4 orders of magnitude out of
   reach at order 7 (`f7/README.md`), and the schedule tree is
   ~1e14-1e15 at budget 42.
