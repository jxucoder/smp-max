# Design: certifying the f(6) enumeration (the last unformalized link)

Status (2026-09-01): design done; Architecture 3 pilot DONE and GO
(order-5 refutation certified end-to-end); order-6 probes DONE and GO
(hardest-region cubes refute in minutes; see "Order-6 probe results").
Remaining: cube-campaign driver + the two Lean layers.

## What is missing, precisely

The Lean development already proves (zero sorries, standard axioms):

- `bridge` : sc(I) ≤ sc(readoff I) for every well-formed order-6 I;
- the validity layer (`chain_complete`, `traj_*`, `wtraj_*`,
  `prevOwner_*`): the read-off trajectory data of every instance is
  realized by a legal schedule within all budgets.

The unformalized residue is a single computational claim:

    (*)  max over all legal schedules S of sc(R(S)) = 48

currently established by `gen_enum.c` (215 lines of C, 26,574,282,886
nodes, ~40–80 core-hours, ≈1–2×10⁵ nodes/core-second) plus the
computational validation matrix. Certifying (*) closes the chain:
f(6)=48 becomes machine-checked end-to-end.

Note the asymmetry with f(5): there the *hypothesis* discharged outside
the kernel was 120 UNSAT certificates checked by a verified checker.
Here the outside-the-kernel object is an enumeration with no natural
per-item certificate. Three architectures follow.

## Architecture 1: trace checker (rejected)

Emit a per-node trace from the C run; validate it with a verified
checker. At 2.66×10¹⁰ nodes even 10 bytes/node is 266 GB, and a checker
that *re-derives* the children of each node to confirm completeness is
already a re-enumeration — the "trace" adds nothing. Degenerates into
Architecture 2. Rejected.

## Architecture 2: verified enumerator, trusted compilation

Write a pure functional enumerator in Lean 4; prove it correct against
the mathematical schedule space; compile it (`lake exe`) and run.

- **Spec theorem** (the hard part, but well-scoped):
  `enumMax = maxSchedule`, where `maxSchedule` is the max of
  `stableCount6 ∘ readoffOfTraj` over an inductively defined schedule
  type (steps = cyclic moves with the Def. 1 side conditions), and
  `enumMax` is the DFS's result. Sub-obligations:
  1. DFS visits exactly the legal schedules (induction on the step
     relation; no symmetry pruning in the verified version — see cost);
  2. the per-node evaluation equals `stableCount6 (readoff ...)`
     (already kernel-computable; prove the array-based fast counter
     equal to the list-based spec);
  3. `readoffOfTraj` of the DFS's trajectory state equals the `readoff`
     of Chain6's validity layer (definitional plumbing).
- **Symmetry question.** The C run prunes by first-appearance labeling
  and backward-commutation (48× tree reduction at order 6). A verified
  replay has two options:
  (a) *no pruning*: tree grows to ~10¹² nodes — likely 1000+ core-days
      even compiled. Not viable.
  (b) *formalize Lemma sym*: (i) adjacent man-disjoint steps commute
      leaving trajectories unchanged (finite trace-monoid argument over
      lists — elementary but fiddly); (ii) relabeling invariance
      (the order-5 `relabel` machinery in `Symmetry.lean` ports
      directly). Estimated at 500–1000 lines of Lean in the style of
      Chain6. This is the real new proof content of Architecture 2.
- **Compute estimate**: compiled Lean with arrays is typically 3–10×
  slower than the C: 150–800 core-hours ≈ 1–4 days on 8 cores. Viable.
- **Trust base**: Lean kernel + the Lean compiler/runtime (the spec is
  kernel-checked; the *run* uses compiled code). Same trust shape as
  every "verified algorithm, trusted extraction" artifact. Strictly
  better than today (C code unverified); strictly weaker than f(5)'s
  certificate story (cake_lpr is verified down to machine code).

## Architecture 3: SAT reduction (reuse the f(5) machinery wholesale)

Do not replay the enumeration at all. Encode

    "some legal schedule S has sc(R(S)) ≥ 49"

as CNF, refute it, check the refutation with cake_lpr, and prove the
encoding faithful in Lean. This *replaces* (*) rather than certifying
it, and lands in exactly the f(5) trust base (kernel + cake_lpr +
printer) — the strongest possible outcome.

- **Encoding sketch** (bounded, like bounded model checking):
  - ≤15 frames (each step moves ≥2 of the 30-move budget);
  - frame state: current matching (6×6 one-hot), per-man visited-woman
    mask, per-woman visited-man mask (36+36+36 bits per frame);
  - step choice per frame: one of the 409 cyclic shapes + a "stop"
    marker; transition clauses implement the cyclic move and the
    no-revisit/per-man-cap side conditions;
  - trajectory-derived read-off comparisons: for man m, rank(w) <
    rank(w') in R(S) is determined by first-visit order of w, w' (and
    trajectory-vs-bottom, bottom canonical order) — encodable with
    order variables over the ≤6 visits;
  - stable-count target: 49 selector slots over the 720 order-6
    matchings with the f(5) selector scheme (nonempty + strictly
    increasing + non-blocking against the derived comparisons):
    49×720 ≈ 35k selector variables.
  - symmetry breaking: encode first-appearance labeling as *clauses*
    (constraining the model, sound because Lean's relabel lemma shows a
    witness can be normalized — the same shape as f(5)'s fix-man0).
- **Faithfulness proof**: same genre as `Faithfulness.lean` but larger
  (transition frames + derived comparisons instead of static tables).
  Estimate 1500–3000 lines. The validity layer (Chain6) supplies the
  witness normalization: any instance with sc ≥ 49 yields, via
  bridge + validity, a legal schedule whose read-off has ≥ 49 stable
  matchings — exactly a satisfying assignment.
- **Solver risk (the unknown)**: the space has ~2.7×10¹⁰ canonical
  schedules; refutation hardness is not predictable from node counts.
  Mitigations: cube on the first 1–2 steps (the 512-shard split maps
  onto cubes directly); fall back to per-cube time limits and hybrid
  (solve easy cubes by SAT, replay hard cubes by Architecture 2).
- **MANDATORY PILOT before committing**: run the same construction at
  order 5 against ground truth — encode "some legal order-5 schedule
  has sc(R(S)) ≥ 17" (≤10 frames, 84 shapes, 17×120 selectors), refute
  it, and cross-check against the certified f(5)=16 and the 498,599-
  node enumeration. If the order-5 formula is not comfortably refuted
  (minutes, not days), Architecture 3 is dead at order 6 and the
  decision defaults to Architecture 2.

## Pilot results (2026-09-01): GO at order 5, end-to-end

`sched_sat.py` (this directory) implements the Architecture 3 encoding.
Validation against ground truth, all single-core (Apple M4 Max):

| order | k  | expected | result | time | decode recount |
|-------|----|----------|--------|------|----------------|
| 3     | 3  | SAT      | SAT    | 0.0s | sc = 3, OK     |
| 3     | 4  | UNSAT    | UNSAT  | 0.0s | —              |
| 4     | 10 | SAT      | SAT    | 0.0s | sc = 10, OK (6 transpositions, full budget) |
| 4     | 11 | UNSAT    | UNSAT  | 0.1s | —              |
| 5     | 16 | SAT      | SAT    | 10.4s| sc = 16, OK (8 transpositions) |
| 5     | 17 | UNSAT    | **UNSAT** | **236s** | —          |

Certificate chain for the order-5 refutation (6,340 vars, 226,651
clauses, no symmetry breaking):

    kissat (proof logging)  236s   -> 683 MB DRAT
    drat-trim               267s   -> s VERIFIED, 4.3 GB LRAT
                                       (54,308 RAT lemmas in core -
                                        not pure RUP; fine for cake_lpr)
    cake_lpr                 83s   -> s VERIFIED UNSAT

Total ~10 single-core minutes. This is simultaneously a fourth
independent confirmation of f(5)=16 (schedule space, certificate-
backed) and the feasibility proof for Architecture 3 at the pilot
scale.

**Order-6 scale plan** (before any solve attempt):
1. *Ladder (sequential-prefix) selector ordering*: the current
   quadratic ordering block would be 48·720·721/2 ≈ 12.5M clauses at
   order 6; prefix variables bring it to ~100k. Mandatory.
2. *Cube on the first 1-2 steps* (the 512-shard split maps onto cubes);
   per-cube time limits, hybrid fallback per REPLAY_DESIGN above.
3. *Symmetry-breaking clauses* (first-appearance labeling), soundness
   via the relabeling lemma; without them the order-6 formula likely
   does not converge.
4. Estimated formula size after (1): ~40k vars, ~1.6M clauses per cube.
   Unknown remains unknown until measured: the 5x10^4-fold node blowup
   from order 5 does not translate linearly to solver time in either
   direction.

## Order-6 probe results (2026-09-01, same day): VIABLE

Ladder rebuild first: order-5 regression strictly improves (k=16 SAT
10.4s -> 0.2s; k=17 UNSAT 236s -> 156s; clauses 227k -> 118k). The
order-6 k=49 formula is 84,882 vars / 2.71M clauses / 46 MB, built in
2 s — the feared 12.5M-clause ordering block is gone.

Probes (single-core M4 Max, kissat, no symmetry-breaking clauses):

| probe                                   | result  | time   |
|-----------------------------------------|---------|--------|
| k=48, full dihedral schedule pinned     | SAT     | 0.2s (decode recount sc=48 OK — order-6 encoding validated) |
| k=48, free search (find a witness)      | unknown | >580s  |
| k=49, no cube (full refutation)         | unknown | >580s  |
| k=49, depth-2 dihedral-prefix cube      | unknown | >560s  |
| k=49, depth-3 dihedral-prefix cube      | UNSAT   | 522s   |
| k=49, depth-4 dihedral-prefix cube      | UNSAT   | 76.5s  |

The depth-3/4 cubes sit in the *hardest* region of the space — the
shard family containing the true extremum — and they refute within
minutes. Scaling is ~6.8x per un-fixed level, extrapolating to a
~45-core-hour raw formula; cube-and-conquer makes it parallel and
robust.

Canonical (first-appearance) prefix counts, from the reference
implementation: 153 at depth 1, 25,339 at depth 2, 1,818,512 at
depth 3.

**Campaign design**: adaptive cube-and-conquer over canonical prefixes
— launch the 25,339 depth-2 cubes with a per-cube time limit; split
timeouts to depth 3 (and 4). Expected order 100–1000 core-hours
(days on 8 cores, or a small cloud burst) — the same magnitude as the
C enumeration, but every cube emits a DRAT checked by
drat-trim + cake_lpr and then deleted (f5-style streaming, ~0.7 GB
transient per hard cube).

**Calibration (2026-09-01, `cube_calibrate.py`)**: 41 depth-2
canonical cubes solved incrementally (CaDiCaL assumptions, 300k-conflict
budget each; formula loads in 0.7s): 38/41 UNSAT with median 2.5s,
mean 5.2s, max 24.5s; 3/41 exceed budget (~70-80s spent) — including
the single canonical disjoint-transposition cube (0,1)+(2,3), the
round-robin gateway (canonical labeling collapses the whole hard
family to this one depth-2 cube plus its siblings under (0,1)).

Refined campaign budget:
- fast 93%: 25,339 x 0.93 x 5.2s = ~34 core-hours;
- hard 7% (~1,850 cubes): either solve at ~1h each (6.8x trend from
  the measured depth-3 522s) = ~1,000 core-hours, or split to depth 3
  (~72 children each, mostly seconds, hard ones 522s -> 77s at
  depth 4) = est. 200-500 core-hours.
- Total: ~250-1,000 core-hours => 1.5-5 days on 8 cores, hours on a
  64-core cloud burst. Certificates add ~1.5x (drat-trim + cake_lpr),
  streamed per cube as in the f(5) loop.

Production note: calibration used incremental assumptions (no proofs);
the campaign proper solves per-cube CNFs (base + cube units) with
kissat proof logging so every cube's refutation is independently
checkable. The driver builds the base once in memory and writes only
the current cube's file per worker.

**Lean critical path** (unchanged in kind, now concrete):
1. Lemma sym in Lean — instance level DONE (2026-09-01, `Sym6.lean`,
   364 lines: `relabel6`/`mapMu6`, WF6 + stability + count invariance,
   zero sorries). Campaign cubes are generated with rule (a) only
   (first-appearance), so the commutation lemma (rule (b)) is NOT on
   the critical path. Remaining: the schedule-level statement (relabel
   a schedule, first-participation σ makes it canonical, read-off
   commutes with relabel6) — lands with the Schedule object;
2. the Schedule object — DONE (`Sched6.lean`); cycle decomposition —
   DONE (`Cycle6.lean`: orbit extraction, `stepDecomp_spec` realizes
   any μ→ν difference as disjoint cyclic steps); chain concatenation —
   IN PROGRESS (`ChainSched6.lean`: `chainSched`/`linkSteps`, endpoint
   threading `linkSteps_foldl_last`, abstract destutter run-collapse,
   block two-valued `scanl_orbits_two_valued` all done; remaining:
   block-column monotonicity → block destutter = [μ(m),ν(m)] → assemble
   across blocks → `strajM = traj`/`wtraj`, with `manOpt = idRow6`
   normalized via Sym6).
   Design discovery: readoffS does NOT commute with relabeling (the
   canonical bottom completion is not equivariant), so the faithfulness
   route avoids count-transport on read-offs entirely. The
   *bottom-agnostic bridge* is DONE (`AbsBridge6.lean`:
   `stable_of_orderPreserving` + count corollary, cross-checked by
   re-deriving the promoted-read-off case in 15 lines); the campaign
   instantiates it at `readoffS` and pushes the 49 witnesses through
   `mapMu6`;
3. encoding faithfulness for the frame/selector CNF (1500–3000 lines,
   `Faithfulness.lean` genre), with Chain6's validity layer supplying
   the witness schedule from any 49-matching instance and the
   bottom-agnostic bridge supplying the 49 selector targets;
4. a Lean `export_cnf`-style printer so the campaign formulas are
   printed from Lean definitions (single source of truth, as in f5).

Verdict: Architecture 3 is GO at order 6. No blocker identified;
remaining work is (a) the cube-campaign driver + compute budget, and
(b) the two Lean layers above.

## Recommendation

Two-track, pilot-first:

1. **Order-5 SAT pilot** — DONE, see above: refutation + full
   certificate chain in ~10 single-core minutes. Architecture 3 is GO
   at pilot scale; next gate is an order-6 cube probe after the ladder
   encoding.
2. **Fallback / parallel**: formalize Lemma sym (the 500–1000 line
   commutation + relabeling layer) — needed by Architecture 2 anyway,
   and it strengthens the paper's validation story regardless.
3. Decision point after the pilot; do not start the big faithfulness
   proof until the solver feasibility is known.

## Non-goals

- Certifying the *historical* run: worthless; only re-derivation counts.
- CakeML end-to-end (verified compilation of the enumerator): the
  right theory, wrong cost for this project.
- Verifying monotonicity to restrict to maximal schedules: the all-node
  campaign made it unnecessary; keep the lemma set minimal.
