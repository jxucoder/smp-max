# smp-max: certified maximum numbers of stable matchings

Machine-checkable proofs for f(n) = max number of stable matchings of an
n x n stable-marriage instance (Knuth 1976, Research Problem #5;
Gusfield-Irving 1989, Open Problem #1).

- **[f5/](f5/)** — done (computational phase): independent confirmation of
  f(5)=16 with the first proof certificate. Lean formalization pending.
- **[f6/](f6/)** — open: the conjecture f(6)=48 (OEIS A357271). Staging.

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
- f(6): open; best lower bound 48 (dihedral Latin instance,
  [A351413](https://oeis.org/A351413)); conjectured exact
  ([A357271](https://oeis.org/A357271)).
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

## Next steps

1. Lean 4: formalize encoding faithfulness + the fix-man0 symmetry lemma;
   import the LRAT certificate (note: core has 2,490 RAT lemmas, Mathlib's
   `lrat_proof` is RUP-only — re-solve without RAT-introducing
   inprocessing, convert, or use a RAT-capable checker such as
   LRAT-Catcher, arXiv:2607.00815).
2. Paper: `f5/paper/f5.tex` (draft compiled; hold arXiv until Lean done).
3. Courtesy email to Dan Eilers before anything goes public.
4. Phase 2: see `f6/README.md`.
