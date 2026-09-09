# Archived documents

Process documents from the 2026-08-31 to 2026-09-09 work on f(5), f(6)
and f(7), moved here in the 2026-09-09 restructure. They are kept
verbatim: nothing in them was rewritten when they were moved, so paths
in their bodies refer to the tree as it was at the time (in particular
`f5/lean/SmpF5/` for what is now `lean/SmpF5/`, and `f6/gen_enum.c`,
`f6/FAITHFULNESS_PLAN.md`, `f6/REPLAY_DESIGN.md`, `PLAN.md`, `NOTES.md`,
`INSIGHTS.md` at their old locations, and `f6/README.md` for the attack
log). Nothing here is needed to verify a
result: the current evidence ledger is `STATUS.md`, the recipe is
`VERIFYING.md`, and the retrospective is `docs/INSIGHTS.md`. None of these
files is trusted by any claim (`STATUS.md`, "Not trusted").

| file | what it was | dates | superseded by |
|---|---|---|---|
| `PLAN-2026-09-08.md` | The finish plan written after the 2026-09-08 review: A, the order-6 faithfulness theorem in Lean (file and lemma table); B, the remaining Lean-versus-journal identity checks; C, documents and papers; D, execution order; E, risks. Its status block records every item as done. | 2026-09-08 to 2026-09-09 | `STATUS.md` (what is established and what remains), `PUBLISHING.md` (the publication steps), `lean/SmpF5/README.md` (the module map the plan's table anticipated). |
| `NOTES.md` | The chronological lab notebook: the f(5) results log (encodings, solver and checker runs, the RUP-only re-solves), the f(4) sanity checks and the A344669 confirmations for n = 3 and n = 4, moved out of the root `README.md` when the repository was prepared for release. Append-only and already labelled historical. | 2026-08-31 to 2026-09-08 | `STATUS.md` (the A344669 row cites it for the n = 3, 4 confirmations), `f6/CAMPAIGN.md`, `docs/INSIGHTS.md`. |
| `f6-ATTACK_LOG.md` | The order-6 attack log, formerly `f6/README.md`: what was known, why the f(5) method does not scale directly, the campaign log, the proof-skeleton status, the exhaustive enumeration of the schedule space and its methodology validation, the 2026-09-01 result statement (later marked "superseded as evidence"), and the attack plan. Its opening paragraph was the pre-restructure evidence summary. | 2026-08-31 to 2026-09-08 | `f6/README.md` (the rewritten directory entry point), `STATUS.md` (evidence and numbers), `f6/CAMPAIGN.md`; the enumeration code is `f6/exploration/gen_enum.c`. |
| `f6-FAITHFULNESS_PLAN.md` | Revision 2 of the plan for the Lean proof that the order-6 schedule CNF is faithful (sections 0–11, lemmas L3.x to L7.x), with the progress log of what was built. Complete: the theorem it planned is `f6_eq_48_of_unsat`. Kept whole and unrenumbered because nine Lean module docstrings cite its section and lemma numbers. | 2026-09-02 to 2026-09-08 | The proof itself: `lean/SmpF5/SmpF5/Bridge6.lean` and the faithfulness layer listed in `lean/SmpF5/README.md`. |
| `f6-REPLAY_DESIGN.md` | The design note on certifying the order-6 enumeration, then the last unformalized link: three architectures, the order-5 pilot and the order-6 probes for Architecture 3 (a cube campaign over the schedule CNF with per-cube LRAT certificates), which was the one executed. Still cited by name from `f6/sched_sat.py`, `f6/cube_campaign.py` and `SchedCNF6.lean`. | 2026-09-01 to 2026-09-02 | `f6/CAMPAIGN.md` (the campaign as run), `lean/SmpF5/SmpF5/SchedCNF6.lean` (the formula in Lean), `STATUS.md`. |
| `f6-campaign-FANOUT.md` | The fan-out record of the certificate campaign: the split into eight shards, where each ran, and the merge-and-audit procedure. Contains branch, session and routine identifiers of the run. | 2026-09-05 to 2026-09-06 | The merged journal `f6/campaign/campaign.jsonl.gz` with its audit `f6/campaign/audit_final.txt`, and the provenance section of `f6/CAMPAIGN.md`; `f6/merge_journals.py` is the merge tool. |
