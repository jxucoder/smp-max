# smp-max: certified maximum numbers of stable matchings

Let f(n) be the maximum number of stable matchings of an n × n
stable-marriage instance (Knuth 1976, Research Problem 5; Gusfield and
Irving 1989, Open Problem 1). This repository contains

- the first **machine-checked proof of f(5) = 16** — one Lean 4 theorem
  whose only hypothesis is discharged by 120 SAT certificates checked by
  the formally verified checker cake_lpr;
- the **determination of f(6) = 48**, previously open (conjectured in
  OEIS [A357271](https://oeis.org/A357271)) — a schedule reduction
  formalized in Lean plus a complete, audited SAT certificate campaign
  over the reduced space (318,736 cake_lpr-checked certificates);
- a new **lower bound f(7) ≥ 85**, improving the best published bound
  of 81, with instances checked three independent ways.

## Results

| n | f(n) | what this repository establishes | where |
|---|---|---|---|
| 1–4 | 1, 2, 3, 10 | classical; f(4) = 10 re-proved as a sanity check of the tooling | `f5/` |
| 5 | **16** | machine-checked, end to end: Lean theorem `f5_eq_16_of_unsat` (zero sorries, standard axioms) + 120 Lean-printed cube formulas, each refuted and each certificate accepted by cake_lpr | `f5/`, `VERIFYING.md` |
| 6 | **48** | resolved: reduction lemmas proved in Lean (zero sorries), the reduced space refuted cube by cube (25,493 root cubes, 318,736 certificates, `--audit` exit 0), lower bound from the dihedral instance; the faithfulness theorem tying the formula to the Lean statement is in progress | `f6/`, `f6/CAMPAIGN.md` |
| 7 | **≥ 85** | new lower bound (previous: 81, Ong et al. 2024); two length-20 transposition schedules, verified by brute force, by an independent recount, and via the rotation poset | `f7/` |

## What exactly is machine-checked

**f(5) = 16.** The trust base is the Lean 4 kernel, the axioms
`propext`, `Classical.choice`, `Quot.sound`, about forty lines of
definitions stating what a 5 × 5 instance and a stable matching are,
one LRAT checker (we used cake_lpr, verified down to machine code; any
checker can be substituted), and a 30-line DIMACS printer. The solver
runs are not trusted: their output is what the checker checks. Anyone
can regenerate the 120 formulas from the Lean definitions and re-check
them in two to three hours; `VERIFYING.md` is the recipe.

**f(6) = 48.** Three layers, with different trust levels, stated plainly:

1. *Reduction (Lean theorems, zero sorries).* Every well-formed order-6
   instance has at most as many stable matchings as the read-off
   instance of some *legal schedule* — a sequence of cyclic partner
   swaps from the identity matching obeying the rotation-theory budgets
   (`validity_unconditional`, `bridge`, `chain_complete`, … in
   `f5/lean/SmpF5/SmpF5/*6.lean`). This shrinks the search space from
   about 10^28 instances to about 2.7 × 10^10 schedules.
2. *Refutation of "some legal schedule has ≥ 49" (certificates).* The
   statement is a CNF formula defined in Lean (`SchedCNF6`) and printed
   byte-identically to DIMACS. Its 25,493 canonical root cubes, and the
   children of every cube that had to be split, were all refuted by
   CaDiCaL and every certificate was accepted by cake_lpr: 321,492 cubes,
   318,736 certificates, 0 satisfiable, and the journal audit reports
   every root covered with no bad record. The cube list is also defined
   in Lean and prints byte-identically to the one the campaign ran. The
   certificates (about 20 TB) were deleted after checking; each record
   keeps the SHA-256 of its formula and of its certificate, so any cube
   can be re-derived from Lean and re-checked. An exhaustive direct
   enumeration of all 26,574,282,886 schedules, run earlier, also gives
   a maximum of 48; the certificate campaign supersedes it as evidence.
3. *Faithfulness (in progress).* What is not yet a theorem is that the
   formula encodes "the read-off count is at least 49" — the analogue of
   the f(5) faithfulness proof. About half of it is done
   (`f6/FAITHFULNESS_PLAN.md`, progress log). Until it lands, f(6) = 48
   rests on the Lean reduction, a validated encoding (a positive control
   at 48 is satisfiable and decodes to the extremal schedule), and the
   audited certificates — not on a single Lean theorem as f(5) does.

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

then `#print axioms f5_eq_16_of_unsat` (expect the three standard
axioms), regenerate and refute the 120 f(5) cubes with any
DRAT/LRAT-producing solver and any checker you trust, and for f(6):

```bash
gunzip -k f6/campaign/campaign.jsonl.gz
python3 f6/cube_campaign.py --audit --journal f6/campaign/campaign.jsonl   # exit 0 iff every root cube is certified
```

Any cube can be re-derived from the Lean definitions
(`export_sched_cnf OUT --prefix=<cube id> [--stop]`), re-solved, and
re-checked; its SHA-256 must match the journal. The lower bounds are
checkable in seconds: `python3 smp.py` (validates the counter on the
OEIS extremal instances) and the instances in `f5/paper/f5.tex`,
`f6/README.md`, `f7/lb85.txt`.

## Repository layout

| path | contents |
|---|---|
| `smp.py` | brute-force stable-matching counter, validated on the OEIS A351413 extremal instances |
| `encode.py` | the direct SAT encoding of "some n × n instance has ≥ k stable matchings" used for f(4) and f(5) |
| `f5/` | f(5) = 16: `lean/SmpF5/` (the Lean development — it also hosts the order-6 files), cube runs and checker logs (`cubesL/`), paper (`paper/f5.pdf`) |
| `f6/` | f(6) = 48: `sched_sat.py` (the schedule CNF), `cube_campaign.py` (driver, audit), `campaign/` (final journal, audit outputs, live dashboard), `gen_enum.c` (the direct enumeration), papers (`paper/f6.pdf`, `theory.pdf`), design notes |
| `f7/` | f(7) ≥ 85: `sched_hunt.py`, `lb85.txt`, `README.md` |
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
notified. The publication checklist is in `INSIGHTS.md`. Planned:

1. Finish the Lean faithfulness proof for the order-6 formula, so that
   f(6) = 48 becomes a single theorem with the certificates as its only
   hypothesis.
2. Archive the f(5) certificates and the f(6) journal (Zenodo DOI, GitHub
   release); make the repository public; submit both papers.
3. The general-n conjecture (extremal instances come from all-size-2
   schedules, at full budget for even n) — Conjecture 1 in
   `f6/paper/f6.pdf`.
4. Lower bounds at odd orders 9 to 15 with the schedule search of `f7/`.

## Citing and license

A `CITATION.cff` and a license file will be added before the repository
is made public. Until then, please contact the author before citing.
