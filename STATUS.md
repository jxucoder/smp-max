# Status: what is established, by what evidence, and what is next

Last updated 2026-09-08. This is the evidence ledger of the project: for
each claim, the kind of evidence behind it, the cross-checks that guard
against systematic error, and the ordered list of what remains. It is
meant to be updated whenever a row changes.

## Three kinds of evidence

The repository uses three kinds of evidence, and they are not
interchangeable:

- **Kernel-checked theorem.** A statement verified by the Lean 4 kernel
  from the definitions, resting only on the axioms `propext`,
  `Classical.choice`, `Quot.sound`. Anyone can re-run the check
  (`lake build`, `#print axioms`).
- **Checked certificate.** A proof of unsatisfiability of a specific
  DIMACS formula, verified by cake_lpr, a checker whose own correctness
  is proved down to machine code. The solver that produced it is not
  trusted; only the checker's verdict is.
- **Validated computation.** A program whose output agrees with
  independent programs and known values but has not itself been proved
  correct.

## The ledger

| claim | kernel-checked theorem | checked certificates | validated computation only |
|---|---|---|---|
| **f(5) = 16** | the whole chain: `f5_eq_16_of_unsat` (`f5/lean/SmpF5/SmpF5/Lower.lean`), whose only hypothesis is "these 120 Lean-defined cube formulas are unsatisfiable"; the witness is a kernel-only theorem (`Witness.lean`, axiom `propext` only) | 120 of 120 cubes, cake_lpr `s VERIFIED UNSAT` (`f5/cubesL/cubesL_results.txt`) | none |
| **f(6) ≤ 48** | the reduction: every well-formed order-6 instance is dominated by the read-off of a legal schedule (`validity_unconditional`, `bridge`, `chain_complete`; 243 theorems, 5,230 lines in `f5/lean/SmpF5/SmpF5/*6.lean`, zero sorries) | all 25,493 root cubes of the schedule formula `SchedCNF6.schedCNF49`, directly or via their split subtrees: 321,492 cubes, 318,736 certificates, 0 SAT, `cube_campaign.py --audit` exit 0 (`f6/campaign/audit_final.txt`, `f6/CAMPAIGN.md` "Result") | **faithfulness** of the formula (that a satisfying assignment yields an instance with ≥ 49 stable matchings) — proof in progress, see below; also the earlier direct enumeration of all 26,574,282,886 schedules, maximum 48 (`f6/gen_enum.c`) |
| **f(6) ≥ 48** | — | — | the dihedral instance, recounted at 48 by three independent programs (`smp.py`, `rotation_poset.py`, `sched_sat.readoff_counts`) |
| **f(7) ≥ 85** | — | — | two explicit instances (`f7/lb85.txt`), each counted at 85 by brute force, by an explicit all-blocking-pairs recount, and via the rotation poset's downsets |
| **A344669(3,4,5) = 1092 / 144 / 507,254,400** | — | — | independent SAT enumeration (`f5/cube_enum.py`, `f5/enum_results.txt`), confirming Eilers' unreplicated counts |

## What guards the f(6) certificate layer against systematic error

1. **Single source of truth for the formula.** The CNF is defined in Lean
   (`SchedCNF6.lean`, a line-by-line transcription of `f6/sched_sat.py`)
   and printed by `export_sched_cnf`; the Lean output is byte-identical
   to the Python writer's (base formula sha256 `28421fb6…`, 84,882
   variables, 2,709,212 clauses).
2. **Per-record provenance.** Every one of the 318,736 verified records
   carries the sha256 of its formula, hashed before solving, and of its
   certificate, hashed before checking, plus the solver's and checker's
   return codes and verdict strings. Four cubes (open and closed) were
   re-exported from Lean on 2026-09-08 and matched their journaled
   hashes; a full re-export of all cubes is item 3 below.
3. **Cube-list identity.** The root cubes and the split children are
   defined in Lean (`Cubes6.lean`) and print byte-identically, in the
   same order, to the driver's 25,493 root ids and to the 295,999
   children of all 2,756 journaled splits (`export_cubes6`).
4. **The audit.** `cube_campaign.py --audit` recomputes the root set,
   checks that every root is `verified` or `split` with all children
   recursively covered, and checks every verified record's fields:
   solver rc 20, `cake_rc 0` with `s VERIFIED UNSAT`, no kill flag,
   well-formed hashes. Final verdict:
   `roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0`.
5. **Positive control (encoding not vacuous).** With the dihedral
   schedule pinned, the formula at k = 48 is satisfiable; the model
   decodes to exactly that schedule with 48 distinct selected matchings
   and an independent recount of the read-off gives 48; the same cube at
   k = 49 is unsatisfiable.
6. **Agreement across unrelated methods.** The certificate campaign,
   the direct enumeration of the schedule space, and hill-climbing over
   instances and over schedules (> 10^9 evaluations) all top out at 48;
   the same machinery reproduces f(3), f(4), f(5) = 3, 10, 16, the last
   against this repository's own certified theorem.

## What the f(6) evidence does not yet include

No theorem states that a satisfying assignment of `SchedCNF6.schedCNF49`
yields a legal schedule whose read-off has at least 49 stable matchings.
Until it does, the certificates are not the hypothesis of a Lean theorem,
and f(6) = 48 rests on the Lean reduction + a validated encoding + the
audited certificates, rather than on a single kernel-checked statement as
f(5) does. That is the only difference between the two rows.

Progress on that theorem (plan: `f6/FAITHFULNESS_PLAN.md`, progress log
at the top): 7 of 12 files exist — `Cubes6`, `Decode6`,
`DestutterPrefix6`, `Shapes6`, `Frames6`, `ReadoffSem6`, `SchedLen6`;
1,803 lines, 131 theorems, zero sorries, standard axioms — covering the
parts the plan ranked riskiest: the cube-list identity, the variable
decode layer, the frame bound (`Legal_length_le_15`), and the crux
lemmas `PM_sem` / `PW_sem` (the derived preference variables equal the
read-off ranks).

## What is next, in order

1. **Finish the faithfulness proof.** Remaining: the coverage lemma
   (every canonical legal schedule fits a campaign cube, including the
   recorded splits), the schedule-level relabeling that makes any legal
   schedule canonical (first-appearance normalization), the twelve
   clause-family satisfaction lemmas, and the assembly into
   `f6_upper_of_unsat`. Estimate: days. When it compiles, the f(6) row
   becomes identical in kind to the f(5) row.
2. **Record the split list in Lean.** The final theorem quantifies over
   the cube set the campaign actually ran, so the 2,756 split decisions
   become a Lean list literal, and the audit's cube set is compared to
   `refineCubes` of it. Bookkeeping; the identity check already shows
   the two sides agree.
3. **Re-export and re-hash every verified cube from Lean.** About half a
   day of CPU (`--audit --expect-cnf-dir`); closes the file-identity
   claim at full scale rather than on four samples.
4. **Publish the evidence.** Archive the f(5) certificates and the f(6)
   journal with a DOI (Zenodo, GitHub release), add a license and a
   `CITATION.cff`, make the repository public, submit both papers
   (`INSIGHTS.md`, publication checklist). `VERIFYING.md` lets a third
   party regenerate everything without trusting any run of ours.
5. **f(7).** The upper bound is out of reach by the certified route
   (measured: ~3.25 × 10^8 depth-3 cubes against a ~1 GB base formula,
   three to four orders of magnitude beyond order 6; `f7/README.md`).
   The productive directions are lower bounds at odd orders 9 to 15,
   where the published bounds look as soft as 81 did, and Conjecture 1
   (extremal instances come from all-size-2 schedules, sub-budget at odd
   orders), which the 85-instances support.

## Numbers behind the ledger

| item | value |
|---|---|
| order-6 campaign, distinct cubes | 321,492 (roots 25,493; depth-3 children 197,758; depth-4 children 96,381) |
| verified certificates | 318,736 |
| splits | 2,756 (depth-2 rate 7.1%, depth-3 rate 0.48%) |
| SAT records | 0 |
| total solver time | 1,076,400 s (median 1.0 s per cube) |
| certificate sizes | median 35 MB, max 9.8 GB; ~20 TB checked and deleted |
| toolchain | CaDiCaL 3.0.1 `c6073042` (`--lrat`), cake_lpr (`cake_lpr_arm8.S` sha256 `95b64883…`) |
| Lean, order-6 reduction layer | 5,230 lines, 243 theorems, zero sorries |
| Lean, faithfulness layer so far | 1,803 lines, 131 theorems, zero sorries |
| CI | `lean-verify`: build, no-sorry grep, axiom checks on 1 + 16 theorems (`.github/workflows/lean-verify.yml`) |
