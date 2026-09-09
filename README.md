# smp-max: certified maximum numbers of stable matchings

Let f(n) be the maximum number of stable matchings of an n × n
stable-marriage instance (Knuth 1976, Research Problem 5; Gusfield and
Irving 1989, Open Problem 1). This repository contains

- the first **machine-checked proof of f(5) = 16** — one Lean 4 theorem
  whose only hypothesis is discharged by 120 SAT certificates checked by
  the formally verified checker cake_lpr;
- the first **machine-checked proof of f(6) = 48**, previously open
  (conjectured in OEIS [A357271](https://oeis.org/A357271)) — one Lean 4
  theorem whose only hypothesis is discharged by 318,736 SAT certificates
  checked by cake_lpr, over a formula and a cube set defined in Lean; the
  verdicts come from a campaign journal that is self-attested (below);
- a new **lower bound f(7) ≥ 85**, improving the best published bound
  of 81, with instances checked three independent ways.

## The theorems

```lean
-- lean/SmpF5/SmpF5/Lower.lean
theorem f5_eq_16_of_unsat
    (H : ∀ row ∈ perms120, ¬ Satisfiable (cubeCNF row)) :
    (∀ I : Inst, WF I = true → stableCount I ≤ 16) ∧
    (∃ I : Inst, WF I = true ∧ stableCount I = 16)

-- lean/SmpF5/SmpF5/Bridge6.lean
theorem f6_eq_48_of_unsat
    (H : ∀ c ∈ finalCubes, ¬ Satisfiable (cubeFormula 49 c)) :
    (∀ I : Inst6, WF6 I = true → stableCount6 I ≤ 48) ∧
    (∃ I : Inst6, WF6 I = true ∧ stableCount6 I = 48)
```

In each theorem the only hypothesis is the unsatisfiability of N
Lean-defined formulas (N = 120 for f(5), N = 318,736 for f(6)), each
refuted with a cake_lpr-checked certificate. Both depend on exactly the
axioms `propext`, `Classical.choice`, `Quot.sound`; zero sorries
(37 imported modules, `lake build` 893 jobs). What you must read: the
definitions `Inst6`, `WF6`, `isStable6`, `stableCount6` at the top of
`lean/SmpF5/SmpF5/SixBridge.lean` (40 lines; the order-5 analogues head
`Faithful.lean`). That is the one human step.

## Results

| n | f(n) | what this repository establishes | where |
|---|---|---|---|
| 1–4 | 1, 2, 3, 10 | classical; f(4) = 10 re-proved as a sanity check of the tooling | `f5/` |
| 5 | **16** | machine-checked, end to end: `f5_eq_16_of_unsat` + 120 Lean-printed cube formulas, each refuted and each certificate accepted by cake_lpr | `lean/`, `f5/`, `VERIFYING.md` |
| 6 | **48** | machine-checked, end to end: `f6_eq_48_of_unsat` + the 318,736 cube formulas of the certified cube set, each printed from the Lean definitions (identity re-checked for every cube) and each refuted with a cake_lpr-accepted certificate; the dihedral witness is a kernel computation | `lean/`, `f6/`, `f6/CAMPAIGN.md`, `VERIFYING.md` |
| 7 | **≥ 85** | new lower bound (previous: 81, Ong et al. 2024); two length-20 transposition schedules, verified by brute force, by an independent recount, and via the rotation poset | `f7/` |

## What exactly is machine-checked

`STATUS.md` is the evidence ledger: each claim, the kind of evidence
behind it, the cross-checks, the campaign numbers, and what remains.

**f(5) = 16.** The trust base is the Lean 4 kernel, the three axioms,
about forty lines of definitions stating what a 5 × 5 instance and a
stable matching are, one LRAT checker (we used cake_lpr, verified down to
machine code; any checker can be substituted), and a 30-line DIMACS
printer. The solver runs are not trusted: their output is what the
checker checks. Anyone can regenerate the 120 formulas from the Lean
definitions and re-check them in two to three hours; `VERIFYING.md` is
the recipe.

**f(6) = 48.** The same shape, one order up. The trust base is the Lean
kernel, the three axioms, the definitions at the top of `SixBridge.lean`,
one LRAT checker, the two printers `ExportSchedCnf.lean` and
`ExportCubes6.lean`, and the campaign journal
(`f6/campaign/campaign.jsonl.gz`); the witness `dihedral6_count` is a
kernel computation. The journal is self-attested: a `verified` record is
the driver's transcription of cake_lpr's verdict, the certificates were
deleted after checking, and each record keeps the SHA-256 of its formula
and certificate, so independently verifying a verdict means re-solving
that cube from the Lean-printed formula. Numbers, the Lean identity
checks, the re-solve sample and the `leanchecker` run: `STATUS.md`.

**f(7) ≥ 85.** A computation, not a proof object: two explicit instances
in `f7/lb85.txt`, each counted at 85 by three structurally different
programs; why order 7 is out of reach for the certified route: `f7/README.md`.

## Verify in 30 minutes

Kernel-check every theorem and confirm there are no holes:

```bash
cd lean/SmpF5 && lake exe cache get && lake build   # Lean 4.33.1 + Mathlib; ends with no errors
grep -rn sorry SmpF5/                               # must print nothing
```

Print the axiom base of both theorems (expected output shown):

```bash
cd lean/SmpF5
printf 'import SmpF5\n#print axioms f5_eq_16_of_unsat\n#print axioms f6_eq_48_of_unsat\n' > /tmp/ax.lean
lake env lean /tmp/ax.lean
# 'f5_eq_16_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
# 'f6_eq_48_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Audit the f(6) journal and print the certified cube set from Lean:

```bash
gunzip -k f6/campaign/campaign.jsonl.gz
python3 f6/cube_campaign.py --audit --journal f6/campaign/campaign.jsonl
# audit: roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0   (exit 0)
cd lean/SmpF5 && lake build export_cubes6
.lake/build/bin/export_cubes6 final.txt --final     # Cubes6.finalCubes: 318,736 ids, equal as a set
                                                    # to the journal's `verified` ids
```

Everything else (the id extraction for that comparison, re-hashing every
cube formula, building the pinned solver and checker, re-solving a cube
sample, the positive control, the full f(5) recipe): `VERIFYING.md`.

## Repository layout

| path | contents |
|---|---|
| `lean/` | the Lean development: `SmpF5/` (package `SmpF5`, both orders; `lean/SmpF5/SmpF5/*.lean`, exporters `ExportCnf`, `ExportSchedCnf`, `ExportCubes6`), `Witness.lean` + `gen_witness.py` (standalone f(5) witness), `attic/` (unimported pilots, not built) |
| `f5/` | f(5) = 16: direct-encoding runs, `cube_run.py`, `cube_enum.py` (A344669 counts, `enum_results.txt`), cube runs and checker logs (`cubesL/`), paper (`paper/f5.pdf`) |
| `f6/` | f(6) = 48: `sched_sat.py` (the schedule CNF), `cube_campaign.py` (driver, audit), `lean_rehash.py`, `rotation_poset.py`, `merge_journals.py`, `CAMPAIGN.md` (campaign reference), papers (`paper/f6.pdf`, `theory.pdf`) |
| `f6/campaign/` | evidence: `campaign.jsonl.gz` (the journal), `audit_final.txt`, `audit_mainrun.txt`, `lean_identity.txt`, `recheck_2026-09-09.{txt,jsonl}`, `leanchecker_2026-09-09.txt`; `tools/` (driver ops scripts, dashboard); `probes/` (dry run, provenance and depth-3 pilots) |
| `f6/exploration/` | corroboration and exploration, not on the evidence path: `gen_enum.c` (direct enumeration; `cc -O2 -o gen_enum_c f6/exploration/gen_enum.c`), enumeration logs (`*.tar.gz`), hill-climb and structure searches, the abandoned direct-encoding CNFs |
| `f7/` | f(7) ≥ 85: `lb85.txt`, `sched_hunt.py`, `logs/`, `README.md` |
| `docs/` | `INSIGHTS.md` (retrospective); `history/` (dated plans, the lab notebook, design notes and the fan-out record, kept verbatim) |
| `smp.py`, `encode.py` | brute-force stable-matching counter (validated on the OEIS A351413 extremal instances); the direct SAT encoding used for f(4) and f(5) |
| `STATUS.md`, `VERIFYING.md` | evidence ledger; third-party verification guide |
| `PUBLISHING.md`, `OEIS_DRAFT.md` | release state and the steps needing the owner's accounts; the OEIS comment texts |
| `LICENSE`, `CITATION.cff`, `.zenodo.json`, `.github/workflows/` | Apache-2.0; citation and deposit metadata; CI (`lean-verify`: build, no-sorry grep, axiom checks on 1 + 25 theorems; `build-papers`) |

Toolchain: Lean 4 `v4.33.1` with Mathlib (about 8 GB in `.lake`), Python 3
(standard library); for regenerating certificates, CaDiCaL `c6073042` and
[cake_lpr](https://github.com/tanyongkiam/cake_lpr) in the gitignored
`cadical-src/`, `cake_lpr-src/` (kissat 4.0.4 + drat-trim in `dt-src/`,
f(5) only). Commits, assembly hashes, build lines: `VERIFYING.md`.

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

The mathematics is finished: f(6) = 48 has been a single Lean theorem
with the certificates as its only hypothesis since 2026-09-08. Not yet on
arXiv; OEIS has not been notified.

Next, in the order of `STATUS.md` "What is next": (1) publish the evidence
(Zenodo DOI, arXiv for both papers, OEIS A357269 / A357271 / A344669; the
account steps are in `PUBLISHING.md`, the texts in `OEIS_DRAFT.md`); (2) a
third-party re-check; (3) lower bounds at odd orders 9 to 15 with the
schedule search of `f7/`; (4) Conjecture 1 of `f6/paper/f6.pdf`.

## Cite

```bibtex
@software{xu2026smpmax,
  author  = {Xu, Jiarui},
  title   = {smp-max: certified maximum numbers of stable matchings
             (f(5) = 16, f(6) = 48, f(7) >= 85)},
  year    = {2026},
  url     = {https://github.com/jxucoder/smp-max},
  version = {1.0.0},
  note    = {arXiv ids to follow}
}
```

Apache License 2.0 (`LICENSE`); `CITATION.cff` carries the same metadata
for GitHub's "Cite this repository", `.zenodo.json` the deposit metadata.
