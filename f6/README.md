# f(6) = 48

**What it rests on.** `f6_eq_48_of_unsat` (`../lean/SmpF5/SmpF5/Bridge6.lean`)
is one Lean 4 theorem, zero sorries, axioms `propext`, `Classical.choice`,
`Quot.sound`:

    (∀ c ∈ Cubes6.finalCubes, ¬Satisfiable (Cubes6.cubeFormula 49 c)) →
      (∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48) ∧ ∃ I, WF6 I = true ∧ stableCount6 I = 48

Its only hypothesis, that every cube formula of the Lean-defined certified
cube set is unsatisfiable, is discharged by cake_lpr-checked certificates
recorded in the campaign journal `campaign/campaign.jsonl.gz` (self-attested:
the driver's transcription of the checker's verdicts, the certificates
deleted after checking). The formula and the cube set were re-derived from
the Lean definitions for every cube (`campaign/lean_identity.txt`), and a
random sample of cubes was re-solved independently on a second machine.
Numbers and the trust statement: `../STATUS.md`; how to re-check any link
yourself: `../VERIFYING.md`.

## Lower bound: the dihedral instance

The dihedral Latin instance of OEIS A351413 (entry = 1-based rank man i
gives woman j; woman j gives man i rank 7 - entry):

    123456
    214365
    365214
    456123
    541632
    632541

Recount it: `python3 ../smp.py` prints `n=6: expected 48, got 48  [OK]`
(brute force over the 720 matchings, alongside three smaller A351413
instances); `python3 rotation_poset.py` recounts it as the downsets of its
15-element rotation poset. In Lean it is the literal `dihedral6` and
`dihedral6_count : stableCount6 dihedral6 = 48`
(`../lean/SmpF5/SmpF5/Lower6.lean`, kernel `decide`), the witness half of
`f6_eq_48_of_unsat`.

## What is in this directory

| path | contents |
|---|---|
| `CAMPAIGN.md` | the campaign reference (result table, toolchain and provenance, Lean-side identity checks, the second-machine re-check), followed by the operational record of the run |
| `sched_sat.py` | the schedule CNF: "some legal order-6 schedule reads off at least k stable matchings"; transcribed line by line into `SchedCNF6.lean`; `readoff_counts` is one of the independent recounters |
| `cube_campaign.py` | the campaign driver: root cubes and split children, the solve / check / delete pipeline, the journal, `--audit`, `--summary` |
| `lean_rehash.py` | recomputes every journaled formula hash from the Lean-printed base formula and unit clauses |
| `merge_journals.py` | merges shard journals for a single audit (SAT > verified > split > non-terminal); the released journal is a single lineage and needed no merge |
| `rotation_poset.py` | rotation-poset extractor: independent recount of the dihedral instance (and of the order-5 witness) |
| `campaign/` | the evidence: journal, audit transcripts, identity and re-check transcripts, `leanchecker` log (`campaign/README.md`); `campaign/tools/` the scripts that ran it, `campaign/probes/` the pilot runs |
| `exploration/` | hill climbing, schedule enumerations (`exploration/gen_enum.c` and its shard logs), calibration, the abandoned direct encoding; corroboration, not on the evidence path (`exploration/README.md`) |
| `paper/` | `f6.tex`, `f6.pdf`: the paper |
| `theory.tex`, `theory.pdf` | working notes of 2026-08-31 on the schedule reduction and the enumeration route; the enumeration is corroboration only, the proof is the theorem above and `paper/f6.pdf` |

## History

The 2026-08-31 to 09-08 attack log that used to be this file
(reconnaissance, hill climbing, the enumeration route, the 2026-09-01
result statement, the attack plan) is archived verbatim as
`../docs/history/f6-ATTACK_LOG.md`. The two plan documents are archived
with it: `../docs/history/f6-REPLAY_DESIGN.md` (which architecture was
chosen for the certificate layer, and the pilots) and
`../docs/history/f6-FAITHFULNESS_PLAN.md` (the Lean proof plan and its
progress log; Lean docstrings cite its section and lemma numbers).
