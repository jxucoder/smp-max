# Project insights — smp-max

**Status: PRIVATE. Owner has decided not to publish yet (2026-09-01).**
Nothing here is on arXiv, OEIS has not been notified, the repo is
private, and no outreach has been made. See "Publication checklist"
below for the day that changes.

## Results

1. **f(5) = 16, first machine-checkable proof.** Lean 4 development
   (zero sorries; axioms propext/Choice/Quot.sound) reduces the theorem
   to 120 Lean-defined CNFs; kissat refutations checked end-to-end by
   the formally verified checker cake_lpr, 120/120. Lower bound is a
   kernel-computed witness. Previously the value rested on one
   unpublished 2022 MiniZinc run. Paper: `f5/paper/f5.pdf`.
2. **f(6) = 48, first determination (previously open).** The schedule
   reduction (three elementary lemmas over Gusfield–Irving rotation
   theory) plus exhaustive evaluation of all 26,574,282,886 schedule
   read-off instances. Confirms the conjecture in OEIS A357271.
   Paper: `f6/paper/f6.pdf`; theory notes: `f6/theory.pdf`.
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
  only at even orders. **Conjecture (in paper #2): for every n>=3, f(n)
  is attained by an all-size-2 schedule; for even n, by a full-budget
  one (n(n-1)/2 transpositions).** If proven, f(n) becomes a clean optimization over
  swap-schedules ("sorting-network-like" objects) and could sharpen
  the 2.28^n..3.55^n asymptotic band — this is the sharpest theoretical
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
  route is 3-4 orders of magnitude out of reach there (`f7/README.md`),
  so cloud sizing was the wrong question. Meanwhile the same schedule
  space is an excellent lower-bound engine: ~20 laptop-minutes of
  hill climbing over size-2 schedules took f(7) from the best known 81
  (Ong et al. 2024) to **85** (`f7/`). Searching only full-budget
  schedules caps at 80 — odd orders live below full budget, exactly as
  Conjecture 1 predicts, so the schedule *length* must be a search
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
  conjecture's odd exclusions).
- **"It felt easy" = correct problem selection**: the work rode on
  mature infrastructure (SAT certificates, cake_lpr, Mathlib, the
  ITP-2024 architecture) at the moment it became cheap, on the smallest
  unclaimed problems of a genre maintained by a single researcher. The
  effort went into *choosing*, verifying, and cross-checking — not into
  any single heroic computation (largest run: ~10 laptop-hours).

## Remaining work (when resumed)

1. Lean certification of the f(6) chain: DONE for the theory layer
   (bridge lemma in SixBridge.lean; lattice/chain theory + the full
   validity/coverage lemma in Lattice6.lean + Chain6.lean — maximal
   chain, cover steps, completeness, trajectory budgets both sides,
   cyclic step structure; zero sorries, standard axioms). Remaining:
   the SAT-reduction route to a certified upper bound is GO at both
   pilot and order-6 probe scale (f6/REPLAY_DESIGN.md: order-5
   refutation certified end-to-end in ~10 min; order-6 hardest-region
   cubes refute in minutes; campaign estimated 100-1000 core-hours).
   Left: cube driver + Lemma sym in Lean + encoding faithfulness.
   **Update 2026-09-08:** the cube campaign is complete and audited
   (318,736 certificates, 0 SAT, exit 0; `f6/CAMPAIGN.md`); the Lean
   faithfulness proof is under way, with the cube-list identity, the
   decode layer, the frame bound and the crux (read-off semantics of
   PM/PW) done - see the progress log in `f6/FAITHFULNESS_PLAN.md`.
2. Paper polish: expand both drafts to venue length; decide venues
   (f5 -> ITP 2027, CFP ~Jan-Mar 2027; f6 -> combinatorics journal or
   SAT/CP).
3. The general-n conjecture (full-budget size-2 extremality) — state
   formally, attempt small-n-generic proof, or publish as open problem.
4. f(7) lower bounds (`f7/`): extend the size-2 schedule search to
   n=9,11,13,15, where the Ong et al. bounds look equally soft. Needs
   an O(n^2) rotation extractor so counting goes through the rotation
   poset's downsets instead of brute force over n! matchings —
   `rotation_poset.extract_rotations` enumerates the lattice and dies
   past n=9.

## Publication checklist (for the day the owner says go)

- [ ] Repo -> public, tag release, LICENSE
- [ ] Regenerate LRAT certificates; Zenodo deposit with DOI
- [ ] arXiv: both papers (companion cross-references), same day
- [ ] OEIS: A357269 add a(6)=48; comment on A357271/A344669 with links
- [ ] Venue submissions; artifact evaluation via VERIFYING.md + CI
- [ ] (Optional) note to Dan Eilers — owner previously decided name
      credit only, no email; revisit at publication time
