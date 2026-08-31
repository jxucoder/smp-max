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
- **Extremals are full-budget, all-size-2, round-robin-like.** At every
  order tested (3..6), the maximizers use the maximum number of
  rotations, all of size 2. The n=6 optimum is the dihedral/round-robin
  schedule; large-rotation regions of the space peak strictly lower.
  **Conjecture (general n): f(n) is attained by a full-budget size-2
  schedule.** If proven, f(n) becomes a clean optimization over
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
- **f(7) is now a budget question, not a wall**: schedule tree ~1e14-1e15
  (budget 42), i.e. cloud-scale compute (this is where Modal finally
  becomes the right answer) plus stronger canonicalization. Lower bound
  71; notably Eilers conjectured exactness only for even orders — f(7)'s
  true value is genuinely uncertain.

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

1. Lean certification of the f(6) chain: bridge lemma (elementary list
   argument), verified replay or certified reimplementation of the
   enumeration. Reuses all f(5) infrastructure.
2. Paper polish: expand both drafts to venue length; decide venues
   (f5 -> ITP 2027, CFP ~Jan-Mar 2027; f6 -> combinatorics journal or
   SAT/CP).
3. The general-n conjecture (full-budget size-2 extremality) — state
   formally, attempt small-n-generic proof, or publish as open problem.
4. f(7) feasibility study if ever desired: canonicalization gains, C
   counting-kernel speedups, cloud sizing.

## Publication checklist (for the day the owner says go)

- [ ] Repo -> public, tag release, LICENSE
- [ ] Regenerate LRAT certificates; Zenodo deposit with DOI
- [ ] arXiv: both papers (companion cross-references), same day
- [ ] OEIS: A357269 add a(6)=48; comment on A357271/A344669 with links
- [ ] Venue submissions; artifact evaluation via VERIFYING.md + CI
- [ ] (Optional) note to Dan Eilers — owner previously decided name
      credit only, no email; revisit at publication time
