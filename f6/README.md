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
- Counterexample hunt: 8 hill-climb workers (`hillclimb.py`) launched,
  2h x 8 cores, seeded from dihedral + random restarts.

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
