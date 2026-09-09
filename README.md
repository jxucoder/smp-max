# smp-max: certified maximum numbers of stable matchings

Let f(n) be the maximum number of stable matchings of an n × n
stable-marriage instance (Knuth 1976, Research Problem 5; Gusfield and
Irving 1989, Open Problem 1). This repository contains

- the first **machine-checked proof of f(5) = 16** — one Lean 4 theorem
  whose only hypothesis is discharged by 120 SAT certificates checked by
  the formally verified checker cake_lpr;
- the first **machine-checked proof of f(6) = 48**, previously open
  (conjectured in OEIS [A357271](https://oeis.org/A357271)) — one Lean 4
  theorem, `f6_eq_48_of_unsat`, whose only hypothesis is discharged by
  318,736 SAT certificates checked by cake_lpr, over a formula and a cube
  set defined in Lean; the verdicts come from a campaign journal that is
  self-attested (see below);
- a new **lower bound f(7) ≥ 85**, improving the best published bound
  of 81, with instances checked three independent ways.

## Results

| n | f(n) | what this repository establishes | where |
|---|---|---|---|
| 1–4 | 1, 2, 3, 10 | classical; f(4) = 10 re-proved as a sanity check of the tooling | `f5/` |
| 5 | **16** | machine-checked, end to end: Lean theorem `f5_eq_16_of_unsat` (zero sorries, standard axioms) + 120 Lean-printed cube formulas, each refuted and each certificate accepted by cake_lpr | `f5/`, `VERIFYING.md` |
| 6 | **48** | machine-checked, end to end: Lean theorem `f6_eq_48_of_unsat` (zero sorries, standard axioms) + the 318,736 cube formulas of the certified cube set, each printed from the Lean definitions (identity re-checked for every cube) and each refuted with a cake_lpr-accepted certificate; the dihedral witness is a kernel computation | `f6/`, `f6/CAMPAIGN.md`, `VERIFYING.md` |
| 7 | **≥ 85** | new lower bound (previous: 81, Ong et al. 2024); two length-20 transposition schedules, verified by brute force, by an independent recount, and via the rotation poset | `f7/` |

## What exactly is machine-checked

(`STATUS.md` is the maintained evidence ledger: each claim, the kind of
evidence behind it, the cross-checks, and the ordered list of what
remains.)

**f(5) = 16.** The trust base is the Lean 4 kernel, the axioms
`propext`, `Classical.choice`, `Quot.sound`, about forty lines of
definitions stating what a 5 × 5 instance and a stable matching are,
one LRAT checker (we used cake_lpr, verified down to machine code; any
checker can be substituted), and a 30-line DIMACS printer. The solver
runs are not trusted: their output is what the checker checks. Anyone
can regenerate the 120 formulas from the Lean definitions and re-check
them in two to three hours; `VERIFYING.md` is the recipe.

**f(6) = 48.** The same shape as f(5), one order up. The trust base is
the Lean 4 kernel, the three axioms, about forty lines of definitions
stating what an order-6 instance and a stable matching are (`Inst6`,
`WF6`, `isStable6`, `stableCount6` at the top of `SixBridge.lean`), one
LRAT checker, the two printers `ExportSchedCnf.lean` and
`ExportCubes6.lean`, and the campaign journal. The theorem
`f6_eq_48_of_unsat` (`Bridge6.lean`) says: if every cube of
`Cubes6.finalCubes` has an unsatisfiable formula `cubeFormula 49 c`, then
every well-formed order-6 instance has at most 48 stable matchings and
the dihedral instance has exactly 48. Inside the kernel it composes

1. the *reduction*: every well-formed order-6 instance is dominated by the
   read-off instance of some legal schedule (`validity_unconditional`;
   11 files, 5,230 lines, 243 theorems), which shrinks the search space
   from about 10^28 instances to about 2.7 × 10^10 schedules;
2. the *faithfulness* layer (19 files, 4,761 lines, 333 theorems): any
   such schedule can be relabeled to first-appearance canonical form
   without lowering the count, every canonical schedule fits one of the
   certified cubes, and the schedule's natural assignment satisfies that
   cube's formula whenever the read-off has at least 49 stable matchings;
3. the kernel-checked witness `dihedral6_count`.

Outside the kernel: the formula `SchedCNF6.schedCNF49` (84,882 variables,
2,709,212 clauses) was refuted over 25,493 root cubes, adaptively split to
321,492 cubes whose 318,736 leaves were all refuted by CaDiCaL with every
certificate accepted by cake_lpr (0 satisfiable; `cube_campaign.py
--audit` exit 0). The certified cube set is a Lean definition
(`finalCubes`, built from the 2,756 recorded split decisions) that prints
exactly the journal's verified ids, and all 321,492 cube formulas the
solver saw recompute byte for byte from the Lean definitions
(`f6/campaign/lean_identity.txt`). The certificates (about 25 TB) were
deleted after checking; each journal record keeps the SHA-256 of its
formula and of its certificate. The journal is self-attested — a
`verified` record is the driver's transcription of cake_lpr's verdict —
so independently verifying a verdict means re-solving that cube from the
Lean-printed formula (about 300 core-hours for the whole tree; the hashes
make a re-run comparable record by record). An exhaustive direct
enumeration of all 26,574,282,886 schedules, run earlier, also gives a
maximum of 48; it is corroboration, not evidence.

**f(7) ≥ 85.** A computation, not a proof object: two explicit instances
in `f7/lb85.txt`, each counted at 85 by three structurally different
programs. The upper bound is open; `f7/README.md` explains why the
certified route used at order 6 is three to four orders of magnitude out
of reach at order 7, and where lower bounds can still be improved.

## Verifying it yourself

`VERIFYING.md` gives the step-by-step recipe. In short:

```bash
cd f5/lean/SmpF5 && lake exe cache get && lake build     # kernel-checks every theorem (f5 and f6 layers)
grep -rn sorry SmpF5/                                     # must print nothing
```

then `#print axioms f5_eq_16_of_unsat` and `#print axioms
f6_eq_48_of_unsat` (expect the three standard axioms for both),
regenerate and refute the 120 f(5) cubes with any DRAT/LRAT-producing
solver and any checker you trust, and for f(6):

```bash
gunzip -k f6/campaign/campaign.jsonl.gz
python3 f6/cube_campaign.py --audit --journal f6/campaign/campaign.jsonl   # exit 0 iff every root cube is certified
cd f5/lean/SmpF5 && lake build export_sched_cnf export_cubes6
.lake/build/bin/export_cubes6 final.txt --final       # the certified cube set: compare with the journal's verified ids
.lake/build/bin/export_sched_cnf base.cnf              # then export_cubes6 units.tsv --units=all_ids.txt and
python3 ../../../f6/lean_rehash.py base.cnf units.tsv ../../../f6/campaign/campaign.jsonl   # every cube formula's hash
```

(`VERIFYING.md` spells out the id extraction.) Any single cube can be
printed in full — an open cube `0,1;2,3` as `export_sched_cnf OUT
--prefix='0,1;2,3'`, a closed cube `0,1;stop` as `--prefix='0,1' --stop`,
the root `stop` as `--stop` alone — re-solved, and re-checked; its SHA-256
must match the journal. The lower bounds are
checkable in seconds: `python3 smp.py` (validates the counter on the
OEIS extremal instances) and the instances in `f5/paper/f5.tex`,
`f6/README.md`, `f7/lb85.txt`.

## Repository layout

| path | contents |
|---|---|
| `smp.py` | brute-force stable-matching counter, validated on the OEIS A351413 extremal instances |
| `encode.py` | the direct SAT encoding of "some n × n instance has ≥ k stable matchings" used for f(4) and f(5) |
| `f5/` | f(5) = 16: `lean/SmpF5/` (the Lean development — it also hosts the order-6 files), cube runs and checker logs (`cubesL/`), paper (`paper/f5.pdf`) |
| `f6/` | f(6) = 48: `sched_sat.py` (the schedule CNF), `cube_campaign.py` (driver, audit), `lean_rehash.py` (re-hash every cube formula from Lean-printed pieces), `campaign/` (final journal, audit outputs, `lean_identity.txt`, live dashboard), `gen_enum.c` (the direct enumeration), `FAITHFULNESS_PLAN.md` (the proof plan and its progress log), papers (`paper/f6.pdf`, `theory.pdf`), design notes |
| `f7/` | f(7) ≥ 85: `sched_hunt.py`, `lb85.txt`, `README.md` |
| `STATUS.md` | evidence ledger: what is established, by what kind of evidence, and what is next |
| `PLAN.md` | the 2026-09-08 finish plan and its status |
| `VERIFYING.md` | third-party verification guide |
| `INSIGHTS.md` | retrospective, open questions, publication checklist |
| `NOTES.md` | the chronological lab notebook |

Toolchain: Lean 4 `v4.33.1` with Mathlib (`lake exe cache get`), Python 3,
and, for regenerating certificates, CaDiCaL at commit `c6073042`
(`cadical-src/`), cake_lpr from
[tanyongkiam/cake_lpr](https://github.com/tanyongkiam/cake_lpr)
(`cake_lpr-src/`), kissat 4.0.4 and
[drat-trim](https://github.com/marijnheule/drat-trim) (`dt-src/`, f(5)
only). The three source directories are gitignored; `f6/CAMPAIGN.md`
records the exact commits and hashes used.

## Background and prior work

- f(1..5) = 1, 2, 3, 10, 16 — OEIS [A357269](https://oeis.org/A357269).
  f(5) = 16 was announced by Dan Eilers (2022, MiniZinc, paper in
  preparation); no proof object existed before this project.
- f(6): open with lower bound 48 (dihedral Latin instance,
  [A351413](https://oeis.org/A351413)), conjectured exact in
  [A357271](https://oeis.org/A357271); resolved here.
- f(7): [A357271](https://oeis.org/A357271) tabulates Thurber's 2002
  composition bounds (71 at order 7); its linked
  [Ong et al. 2024 file](https://oeis.org/A357271/a357271_1.txt) (Ong,
  Ang, Ho, Eilers, Marks, Buzi, IFoRE 2024) improves every odd order by
  hill climbing (81, 365, 1690, 7123, 27059 at orders 7, 9, 11, 13, 15).
  Improved here to 85 at order 7 (checked 2026-09-06 against the entry
  as last edited May 2025).
- General bounds: 2.28^n ≤ f(n) (Thurber 2002), f(n) ≤ 3.55^n
  (Palmer–Pálvölgyi); the first exponential upper bound is Karlin,
  Oveis Gharan and Weber, STOC 2018.
- Certified SAT: cake_lpr (Tan, Heule, Myreen), the verified checker;
  LRAT/DRAT proof formats (Heule et al.).

## Status and roadmap

Not yet published: neither paper is on arXiv and OEIS has not been
notified. The publication checklist is in `INSIGHTS.md`; the dated
roadmap is in `STATUS.md`. The Lean faithfulness proof for the order-6
formula was completed on 2026-09-08 (`PLAN.md`), so f(6) = 48 is a
single theorem with the certificates as its only hypothesis. Planned:

1. Archive the f(5) certificates and the f(6) journal (Zenodo DOI, GitHub
   release); add a license and a `CITATION.cff`; make the repository
   public; submit both papers.
2. An independent re-check: a third party re-solving a sample of cubes
   from the Lean-printed formulas, and a `lean4checker` run.
3. The general-n conjecture (extremal instances come from all-size-2
   schedules, at full budget for even n) — Conjecture 1 in
   `f6/paper/f6.pdf`.
4. Lower bounds at odd orders 9 to 15 with the schedule search of `f7/`.

## Citing and license

A `CITATION.cff` and a license file will be added before the repository
is made public. Until then, please contact the author before citing.
