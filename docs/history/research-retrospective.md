# Project insights — smp-max

Retrospective. Publication state: `../docs/publishing.md`; evidence: `../docs/results.md`.

## Results

1. **f(5) = 16, first machine-checkable proof.** Lean 4 development
   (zero sorries; axioms propext/Choice/Quot.sound) reduces the theorem
   to 120 Lean-defined CNFs; kissat refutations checked end-to-end by
   the formally verified checker cake_lpr, 120/120. Lower bound is a
   kernel-computed witness. Previously the value rested on one
   unpublished 2022 MiniZinc run. Paper: `../papers/f5/f5-max-stable-matchings.pdf`.
2. **f(6) = 48, first determination (previously open; conjectured in
   OEIS A357271).** One Lean theorem, `f6_eq_48_of_unsat`
   (`../lean/SmpMax/Six/ExactMaximum.lean`), whose only hypothesis — the
   unsatisfiability of the Lean-defined cube formulas — is discharged by
   cake_lpr-checked certificates; the exhaustive schedule enumeration is
   corroboration. Numbers and cross-checks: `../docs/results.md`. Paper:
   `../papers/f6/f6-max-stable-matchings.pdf`; working notes: `../papers/notes/f6-schedule-reduction.pdf`.
3. **By-products**: independent confirmation of every previously
   unreplicated number in this OEIS corner — f(4)=10 uniqueness,
   f(5)=16, A344669(3,4,5) = 1092 / 144 / 507,254,400, and the reduced
   count 176,130.

## Mathematical insights

- **Change of universe beats brute force.** The instance space of order
  6 is ~1e28; the schedule space (sequences of cyclic partner swaps
  from the identity, with rotation-theory budgets) is ~2.7e10 — a
  28-orders-of-magnitude compression obtained purely from the classical
  structure theory, no solver cleverness required.
- **The bridge lemma is the whole trick.** Read an instance's stable
  structure off as trajectories, push every non-stable-partner to the
  bottom of each list: original stable matchings survive, count only
  grows. One page of proof; it turns "all instances" into "all
  schedules".
- **Extremals are all-size-2; full-budget exactly at even orders.**
  Computed rotation profiles of the maximizers (2026-09-01): order 3 -
  attained by two transpositions (4 of budget 6; a two-size-3-rotation
  Latin instance also attains it); order 4 - six transpositions, full
  budget 12; order 5 - eight transpositions, 16 of budget 20 (full
  budget provably impossible since f(5)=16); order 6 - fifteen
  transpositions, full budget 30. Matches Eilers conjecturing exactness
  only at even orders. **Conjecture (Conjecture 1 in the f(6) paper):
  for every n>=3, f(n) is attained by an all-size-2 schedule; for even
  n, by a full-budget one (n(n-1)/2 transpositions).** If proven, f(n)
  becomes a clean optimization over swap-schedules
  ("sorting-network-like" objects) and could sharpen the
  2.28^n..3.55^n asymptotic band — this is the sharpest theoretical
  question the project produced.
- **Rotation-poset rigidity.** All 450 sampled order-5 maximizers share
  ONE poset skeleton (8 elements, 21 relations); the 176,130 reduced
  maximizers are one structure realized many ways. Extremality lives in
  the poset, not the preference details.
- **Chain conditions alone don't cap the count** (relaxed search
  reached 54 with only the 2-regular chain-cover constraints);
  partner-trajectory consistency is the binding constraint. Any future
  human-readable proof of f(6)=48 must use it.
- **Read-off does NOT auto-refine large rotations** (0/189): large
  rotations are trajectory-intrinsic. The size>=3 regime had to be
  enumerated, not reduced away (local 3-cycle refinement fails in ~1/1000
  cases).
- **f(7): the lower bound is cheap, the upper bound is not.** The
  schedule tree is ~1e14-1e15 (budget 42), and the *certified* cube
  route is 3-4 orders of magnitude out of reach there
  (`../docs/f7.md`), so cloud sizing was the wrong question. Meanwhile
  the same schedule space is an excellent lower-bound engine: ~20
  laptop-minutes of hill climbing over size-2 schedules took f(7) from
  the best known 81 (Ong et al. 2024) to **85** (`../f7/`). Searching
  only full-budget schedules never exceeded 80 in the logged runs
  (`../results/f7/search/`, 10 seeds) — odd orders live below full budget, exactly
  as Conjecture 1 predicts, so the schedule *length* must be a search
  variable.
- **Conjecture 1 gets external support.** The published record
  instances at n=7 (81 SM, 18 of 21 rotations) and n=9 (365 SM, 32 of
  36) are BOTH all-size-2 and both sub-budget, as are our 85-instances
  (20 of 21). Four independent confirmations of the all-size-2 half,
  and of the odd-order sub-budget pattern, from data this project did
  not generate.

## Methodological insights

- **Certified results as test oracles.** The f(5) theorem (certified via
  Lean) later served as ground truth to validate the f(6) enumeration
  machinery (which reproduces 3/10/16 at orders 3/4/5). Building the
  certified small case first paid for itself.
- **The validation matrix pattern**: ground-truth reproduction +
  independent reimplementation + symmetry-reduction on/off comparison
  (identical maxima at 4.5x/14x/48x tree blowups) + multiple unrelated
  search spaces agreeing. Each check is cheap; together they exceed the
  evidence standard of most published computational results.
- **Cross-checks catch bugs in minutes**: a missing bottom-completion
  once produced a fake "best 167" — immediately suspicious because it
  dwarfed all independent evidence, found and fixed within minutes.
  Single-pipeline projects would have celebrated a false counterexample.
- **Single source of truth for encodings**: defining the CNFs in Lean
  and printing them for the solvers eliminated the classic "does the
  encoding match the formalization" gap in certified-SAT papers.
- **Comment sections beat wikis beat memory**: three times the project
  pivoted because the authoritative source (OEIS entries, problem-page
  comments) contradicted secondary sources or my initial assumptions
  (#835 already solved; f(5) already computed; the a(6)-exactness
  conjecture's odd exclusions). The same lesson recurred at order 7: the
  "best known" 71 quoted here for weeks was two years stale
  (`../docs/f7.md`).
- **"It felt easy" = correct problem selection**: the work rode on
  mature infrastructure (SAT certificates, cake_lpr, Mathlib, the
  ITP-2024 architecture) at the moment it became cheap, on the smallest
  unclaimed problems of a genre maintained by a single researcher. The
  effort went into *choosing*, verifying, and cross-checking — not into
  any single heroic computation. (Largest run: the order-6 certificate
  campaign, about 300 core-hours of solver time plus cake_lpr checking,
  median 1.0 s per cube, spread over three machines; the enumeration took
  about 10 hours on 8 cores; everything else was minutes. Numbers:
  `../docs/results.md`.)

## Open questions

What remains to do, in order, is `../docs/results.md` ("What is next"); the
publication steps are `../docs/publishing.md`. The open mathematical questions
this project leaves behind are Conjecture 1 above and the lower bounds at
odd orders 9 to 15, where the published bounds look as soft as 81 did
(`../docs/f7.md`).
