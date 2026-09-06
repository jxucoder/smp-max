# f(7): lower bounds are cheap, the certified upper bound is not

Two findings from a 2026-09-06 review of what f(6) taught, both of which
change what is worth doing at order 7.

## 1. Our state of the art was two years stale — and the real one is beaten

`README.md` and `INSIGHTS.md` quoted **71** as the best known lower bound
for f(7). That is Thurber's 2002 composition bound (OEIS
[A357271](https://oeis.org/A357271)). The same OEIS entry links a 2024
file, [`a357271_1.txt`](https://oeis.org/A357271/a357271_1.txt) — Ryan
Ong, Bethany Ang, Abigail Ho, Dan Eilers, Justin Marks, Genti Buzi,
*Improved Hill Climbing for the Stable Marriage Problem*, IFoRE 2024
poster — which improves **every odd order**:

| n | Thurber 2002 | Ong et al. 2024 | here |
|---|---|---|---|
| 7  | 71     | **81**    | **85** |
| 9  | 330    | 365       | — |
| 11 | 1231   | 1690      | — |
| 13 | 6720   | 7123      | — |
| 15 | 25011  | 27059     | — |

Even orders are unimproved, so f(6)=48 is still the best lower bound at
order 6 and this repository's main result is unaffected.

`smp.stable_matchings` reproduces their order-7 instance at exactly 81,
which validates our counter at n=7 against external ground truth.

## 2. f(7) >= 85

`sched_hunt.py` is `f6/struct_hunt.py` generalized to any n, with one
change that turns out to be the whole point: **the schedule length is a
search variable**, not fixed at the full budget of n(n-1)/2
transpositions.

- Restricted to full-budget schedules (all 21 transpositions of K7), the
  search plateaus at exactly **80** — 4 of 10 seeds converge there.
- With the length free: **24 of 24 seeds reached >= 81** and **6 reached
  85**, over two batches (12 seeds x 300 s, 12 seeds x 900 s, one core
  each). Every 85 was found at schedule length 20. No seed ever exceeded
  85, so 85 is plausibly the size-2 optimum at order 7 — and, if
  Conjecture 1 holds, f(7) itself.

Both 85-instances are all-size-2 with **20 of 21 rotations** (40 of the
42 move budget) — sub-budget, exactly as Conjecture 1 predicts for odd
orders, which is why the full-budget search could not see them.

Instances and schedules: `lb85.txt`. Reproduce with

    python3 f7/sched_hunt.py 7 <seed> <seconds>
    python3 f7/sched_hunt.py 6 0 25      # sanity: reaches 48 = f(6)

**Verification.** Both instances were checked three structurally
different ways, all agreeing on 85:

1. `smp.stable_matchings` (brute force over all 5,040 permutations, the
   counter validated against OEIS A351413 at n=3,4,5,6);
2. a naive recount with no early exit that tests every (m,w) pair for
   blocking explicitly — same 85 matchings, not just the same count;
3. Birkhoff: `rotation_poset.count_downsets` of the extracted rotation
   poset = 85.

Preference lists were checked to be genuine permutations on both sides.

Caveat: "new record" rests on the OEIS entry as fetched 2026-09-06 (last
edited May 2025), which still lists the 2024 poster as the improvement.
A literature check is worth doing before claiming it anywhere public.

## 3. Conjecture 1 gets four independent confirmations

The published record instances were never profiled by this project. They
are all all-size-2, and the odd orders are all sub-budget:

| instance | SM | rotations | of max | all size 2? |
|---|---|---|---|---|
| Ong et al. n=7  | 81 | 18 | 21 | yes |
| Ong et al. n=9  | 365 | 32 | 36 | yes |
| ours n=7 (A)    | 85 | 20 | 21 | yes |
| ours n=7 (B)    | 85 | 20 | 21 | yes |

n=11, 13 and 15 could not be profiled: `rotation_poset.extract_rotations`
builds the lattice by brute force over n! matchings. An O(n^2) rotation
extractor (standard Gusfield–Irving) would make those three free, and is
a prerequisite for pushing lower bounds past n=9 anyway.

## 4. Why the certified cube campaign does not scale to order 7

Measured, not estimated. The canonical-prefix counter reproduces the
documented order-6 layers exactly (153 / 25,339 / 1,833,929):

| | n=6 | n=7 |
|---|---|---|
| cyclic shapes | 409 | 2,365 |
| frame bound F | 15 | 21 |
| move budget | 30 | 42 |
| canonical depth-1 | 153 | 873 |
| canonical depth-2 | 25,339 | 817,651 |
| canonical depth-3 | 1,833,929 | ~3.25e8 (sampled, ±0.5%) |
| children per depth-2 node | 72 | 397 |
| pairwise-AMO clauses alone | 1.26M | 58.8M |

At order 7 a depth-2 cube fixes 2 of up to 21 steps against a 42-move
budget — far weaker than at order 6 — while the base formula is ~20x
bigger, so essentially every depth-2 cube would split. The realistic root
layer is depth 3: **~3.25e8 cubes**, each with a per-cube floor of tens of
seconds against a ~1 GB base. That is >= 2 million core-hours *assuming
every cube closes immediately*. Three to four orders of magnitude out of
reach, not a budget question.

Two things from the order-6 campaign that should be fixed before any
formula of this shape is scaled again:

- **46% of the order-6 base CNF is a pairwise at-most-one** on the shape
  alphabet (`sched_sat.py:84-86`: 15 x C(410,2) = 1,257,675 of 2,709,212
  clauses). A ladder encoding is ~18,450. At order 7 the same family
  alone is 58.8M clauses versus ~149k. It cannot be fixed mid-campaign —
  changing a clause changes the base sha256 and invalidates every
  certificate already earned — so encoding choices freeze at launch.
- **The campaign is certificate-bound, not solver-bound.** 781 of the 863
  order-6 splits were triggered by the LRAT size watchdog and only 11 by
  wall-clock; at depth 3 cake_lpr costs 7.5 s median against a 1.5 s
  solve, and even the easiest cube pays ~2 s re-parsing the 48.7 MB base.
  That floor is per-cube and no amount of splitting gets below it.
