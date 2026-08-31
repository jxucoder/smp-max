# f(6): open. Conjecture f(6) = 48 (OEIS A357271).

Nothing here yet — this directory is the staging ground for Phase 2.

## What is known

- Lower bound: f(6) >= 48, attained by the dihedral-group Latin instance
  (OEIS A351413). Ranking matrix (entry = rank man i gives woman j,
  1-based; woman j gives man i rank 7 - that entry):

  ```
  123456
  214365
  365214
  456123
  541632
  632541
  ```

  Our counter (`../smp.py`) reproduces 48 stable matchings for it.
- OEIS A357271 conjectures 48 is exact (also for n=8,10,12,16).
- Upper bounds: nothing instance-specific; only the general 3.55^n.

## Why the f(5) method does not directly scale

Reduced-instance space grows from ~1e17 (n=5) to ~1e28 (n=6). Our f(5)
UNSAT run broke only the n! woman-relabeling symmetry (fix man 0's list).

## Campaign log

**2026-08-31, opening reconnaissance:**
- Rotation-poset microscope (`rotation_poset.py`): the known extremal
  instances have skeletons n=4: 6 elts (2x2x2 tower, 10 downsets);
  n=5 witness: 8 elts, height 4, width 2 (16 downsets); n=6 dihedral:
  **15 elements — the full n(n-1)/2 rotation budget**, height 5,
  width 3 (48 downsets).
- Survey: 450 sampled n=5 maximizers ALL share signature (8 elts,
  21 strict relations) — one skeleton up to iso, strongly suggesting a
  structure theorem "order-5 maximizers = realizations of one poset".
- Consequence for f(6): a 49+ instance must realize a poset on <= 15
  elements with >= 49 downsets; since 15 elements forces all rotations
  to have size exactly 2 (weight budget n(n-1)=30), the fight is over
  poset SHAPE, not size. Candidate route: enumerate weight-feasible
  posets with >= 49 downsets, SAT-check realizability.
- Counterexample hunt round 1 COMPLETE, both spaces capped at 48:
  raw instance space (`hillclimb.py`): 97M evaluations, 14k restarts,
  8/8 seeds best=48, zero counterexamples; structure space
  (`struct_hunt.py`, swap-schedule search): 1.206B evaluations, 72.4M
  valid schedules explored, 8/8 seeds best=48, zero counterexamples.
  Strong empirical support for f(6)=48.
- Next weapon identified: EXHAUSTIVE enumeration of the schedule space
  (DFS over swap sequences with validity pruning + canonicalization by
  commuting independent rotations and man-relabeling) — if the
  full-budget regime enumerates to max 48, and the sub-budget regimes
  (rotations of size >= 3, r < 15) are handled likewise, that plus a
  "reading-off-trajectories does not decrease the count" completeness
  lemma is a full proof skeleton for f(6)=48 — no 1e28 SAT campaign
  needed.

## Proof skeleton status (2026-08-31 evening)

The structural route has nearly closed f(6)=48:
1. **Bridge lemma** (instance count <= its schedule's read-off count):
   proof sketch (non-trajectory pairs bottom-ranked never block; original
   stable matchings survive) + 1500/1500 random instances, 0 violations.
2. **Monotonicity** (extending a schedule never decreases the read-off
   count): 768,472 parent-child pairs, 0 violations.
   => only MAXIMAL schedules need evaluation.
3. **Size-2 regime CLOSED**: exhaustive enumeration of all maximal
   swap-schedules (534 full-budget + 262,241 stuck, bottom-completed)
   in 98s: **maximum = 48**. (`enum_schedules.py`)
4. **Size>=3 reduction, one leak**: every 3-cycle has three 2-swap
   decompositions with identical net effect; on 1122 random valid
   3-cycle schedules, refinement NEVER loses count, but in 1 case all
   three refinements were invalid (revisit conflicts). Closing options:
   commute-then-refine, a direct no-large-rotations-at-extremum lemma,
   or bounded enumeration of large-rotation schedules. (`gen_enum.py`)

Once (1), (2) are proven rigorously and (4) is closed, f(6)=48 follows
from a 98-second enumeration — no 1e28 SAT campaign. All empirical
pillars are cheap to re-verify and Lean-certifiable in principle.

## Attack plan

1. Stronger symmetry breaking: men-relabeling (up to 5! more) and
   side-swap (x2) via lex-leader constraints; needs a soundness lemma.
2. Rotation-poset route: an order-6 instance has at most 15 rotations and
   #stable matchings = #downsets of the rotation poset. "f(6) >= 49"
   implies a realizable rotation poset on <= 15 elements with >= 49
   downsets. Two-level search: candidate posets, then SAT realizability.
3. Incremental targets that are new results even if 48 stays open:
   any concrete upper bound (e.g. f(6) <= 200), or exact maxima over
   structured families (pseudo-Latin, bounded rotation count).
