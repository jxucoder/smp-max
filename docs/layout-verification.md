# Layout migration validation

The 2026-09-09 cleanup reorganizes the checkout from scientific snapshot
`30ad2c3`. It preserves the mathematical claims and their existing limits;
it does not complete the remaining order-6 formalization.

## Preservation checks

| Check | Outcome |
|---|---|
| Lean source comparison | All 31 moved library, exporter, and check files have unchanged code after excluding imports, comments, and formatting. The removed `Basic.lean` was a `hello := "world"` template. |
| Lean build | Both original `SmpF5` and renamed `SmpMax` projects build with the same pinned dependencies. |
| Axioms | The same 17 established theorem checks report exactly `propext`, `Classical.choice`, and `Quot.sound`; the standalone witness reports only `propext`. |
| Separate Lean checks | Standalone order-5 witness, 300 differential count cases with zero mismatches, and the order-4 LRAT pilot pass. |
| Order-5 exports | All 120 upper-bound CNFs, all 120 positive-control CNFs, and the permutation list are byte-identical before and after the moves. |
| Order-6 base | Byte-identical before and after; SHA-256 matches the historical campaign header. |
| Root and split lists | All 25,493 root IDs and 295,999 children of all 2,756 recorded split parents agree between original and renamed Lean and Python implementations. |
| Order-6 sample formulas | Six open/stopped cubes, including depths 3 and 4, are byte-identical before/after and match their historical journal hashes. |
| Campaign audit | Original and renamed drivers both report 321,492 cubes, 318,736 verified records, 2,756 splits, zero missing/bad records, and `audit: OK`. |
| Retained artifacts | All 42 entries in the artifact manifest preserve their original bytes, including journals, logs, archives, historical binaries, and manuscript sources/PDFs. |
| Log deduplication | All 1,024 removed loose log files were byte-compared with their retained archive members. |

The [export comparison data](layout-export-comparison.json) records the
dimensions and hashes. The [migration map](path-migration.md) maps old paths
to current ones; the [artifact manifest](../results/manifest.json) preserves
original file hashes and paths.

## Additional tooling checks

All four saved witnesses recount to 16, 48, 85, and 85 using the independent
matching/poset checks. The order-7 schedules reproduce their stored preferences.
The new certificate runner is tested with controlled subprocesses for
expected UNSAT exit 20, SAT/failing checker rejection, and proof retention.
Those tests validate runner control flow, not mathematical certificates.

Smoke checks cover the Python direct/schedule encoders, small C/Python
enumerations, and the order-5 export-only command. The direct order-4 CNF
also reproduces the retained original bytes. CI now runs documentation,
witness, artifact, runner, campaign-audit, and Lean checks from the new paths.

## Hash clarification

The original guide used `cat cubeL*.cnf`, which includes the 120 positive
controls as well as the 120 upper-bound formulas. It therefore documented
the combined 240-file hash `a93f5e58…`. The upper-bound-only hash is
`044d0edb…`. Both original and renamed exporters give these same hashes;
the formulas did not change.

## Scope

The unchanged formulas did not require a full SAT re-solve. The old LRAT
files remain unavailable and were not independently rechecked during this
cleanup. Full Lean re-export of every one of the 318,736 verified order-6
cubes remains a research task. Paid cloud execution was not launched.
The remaining proof obligations and unlicensed status are unchanged.
