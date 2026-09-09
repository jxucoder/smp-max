# smp-max: maximum numbers of stable matchings

How many stable matchings can a stable-marriage instance have? Let **f(n)**
be the maximum over all instances with n men, n women, and strict, complete
preference lists. This repository studies that question using Lean proofs,
SAT certificates, and independently checked computations.

| Order | Result | Evidence and current limitation |
|---|---|---|
| 5 | **f(5) = 16** | Lean theorem with an explicit UNSAT hypothesis, discharged externally by 120 cake_lpr-checked certificates; kernel-checked lower-bound witness. |
| 6 | **f(6) = 48** | Complete Lean theorem `f6_eq_48_of_unsat`, conditional on checked UNSAT certificates for 318,736 leaf cubes; kernel-checked witness of 48. |
| 7 | **f(7) ≥ 85** | Two explicit witnesses checked by independent matching counts and rotation-poset downsets. The upper bound is open. |

The [evidence ledger](docs/results.md) states exactly what each layer
establishes. An audit of recorded checker verdicts is different from
independently checking regenerated certificates.

## Start here

- **Understand the results:** [order 5](docs/f5.md), [order 6](docs/f6.md),
  [order 7](docs/f7.md), and the [proof architecture](docs/architecture.md).
- **Verify them:** [verification guide](docs/verification.md), including
  prerequisites, expected output, and the trust boundary of each check.
- **Contribute:** [setup and contribution guide](CONTRIBUTING.md),
  [Lean module map](lean/README.md), and [remaining work](docs/roadmap.md).
- **Read the papers:** [order-5 manuscript](papers/f5/f5-max-stable-matchings.pdf),
  [order-6 manuscript](papers/f6/f6-max-stable-matchings.pdf), and
  [manuscript status](papers/README.md).

## Quick verification

From the repository root, with Python 3.9 or later:

```bash
python3 tools/verify_witnesses.py
```

This checks the saved witnesses with counts **16, 48, 85, and 85**. It uses
only the Python standard library, compares the actual matching sets, and
exits nonzero on failure. These counts establish lower bounds.

To build the formal development after installing Lean through elan:

```bash
(cd lean && lake exe cache get)
bash tools/check_lean.sh
```

See the [full verification guide](docs/verification.md) for certificate
regeneration and the completed campaign's journal audit.

## Repository map

| Directory | Purpose |
|---|---|
| [docs/](docs/README.md) | Current explanations, recipes, reference material, and dated history |
| [lean/](lean/README.md) | One Lean project containing the order-5 and order-6 developments |
| [tools/](tools/README.md) | Reusable counters, encodings, verification, and campaign tools |
| [experiments/](experiments/README.md) | Enumeration, alternative SAT runs, and lower-bound searches |
| [results/](results/README.md) | Saved witnesses and immutable evidence, with checksums |
| [papers/](papers/README.md) | Manuscript sources and corresponding PDFs |

New computations write to the ignored `runs/` directory. The
[path migration map](docs/path-migration.md) locates files cited under the
former `f5/`, `f6/`, and `f7/` layout.

## Citation and license

Citation metadata is in [CITATION.cff](CITATION.cff). The manuscripts are
working drafts; their dates and evidence scope are documented alongside them.
No license has been selected for this repository.
