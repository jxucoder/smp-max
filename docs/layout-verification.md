# Layout migration validation

The cleanup incorporates upstream `5e8cb3c`, including the completed
order-6 proof, rebuilt manuscripts and later identity/re-check transcripts.
The earlier migration baseline was `30ad2c3`. Current proof status is in
[the ledger](results.md); file moves are in [the migration map](path-migration.md).

## Proof and formula preservation

| Check | Outcome |
|---|---|
| Lean source comparison | All 44 library, exporter, aggregate and check files preserve upstream code after excluding imports, comments and whitespace. The mathematical declarations and namespaces are unchanged. |
| Lean build | The complete `SmpMax` project and all three exporters build with the same pinned Lean/Mathlib dependencies. |
| Axioms | All 26 theorem checks, including both exact-maximum theorems, use exactly `propext`, `Classical.choice` and `Quot.sound`; the standalone order-5 witness uses only `propext`. |
| Separate checks | Standalone witness, 300 differential count cases with zero mismatches, and the order-4 LRAT pilot pass. |
| Order-5 exports | All 120 production CNFs, 120 positive controls and the permutation list are byte-identical to the pre-cleanup baseline. |
| Order-6 base and cube lists | Base formula, all 25,493 roots and 295,999 children of 2,756 split parents match the pre-cleanup exports and current Python definitions. |
| Final cube set | The renamed Lean definition prints exactly the journal's 318,736 verified leaf IDs, without duplicates. |
| All formula hashes | All 321,492 journaled hashes recompute from current Lean-printed base and unit clauses; zero mismatches or missing units. |
| Campaign audit | 321,492 cubes, 318,736 verified, 2,756 splits; zero missing/bad records and `audit: OK`. The encoder source-hash notice reflects import/doc changes; the formula hash matches. |
| Saved artifacts | All 75 manifest entries match their recorded source commits, including newer manuscripts, identity checks, re-check transcripts and order-7 search logs. |
| Log deduplication | The original 1,024 loose enumeration logs were byte-compared against retained archive members. |

The [export comparison data](layout-export-comparison.json) records hashes
and counts. Run `bash tools/check_lean.sh` and
`python3 tools/campaign/check_lean_identity.py` to reproduce the formal and
campaign checks. The [manifest](../results/manifest.json) records source
commit, original path, checksum and size for each immutable artifact.

## Tooling and documentation

All four witnesses recount to 16, 48, 85 and 85 using independent matching
and poset checks. The order-7 schedules reconstruct the saved preferences.
Three certificate-runner tests cover success, solver/checker failures and
proof retention. The order-5 export-only command, Python encoders and small
enumeration/search probes were checked. Local documentation links pass.
CI builds and checks Lean, audits the journal, verifies artifact hashes and
witnesses, tests the certificate runner, and compiles the relocated papers.

## Hash clarification

`cat cubeL*.cnf` includes 120 production CNFs and 120 positive controls:
its combined hash is `a93f5e58…`. The production-only hash is `044d0edb…`.
Both original and relocated exporters give these hashes.

## Scope

No full SAT re-solve was performed for this cleanup. The deleted original
certificates remain unavailable; journal auditing and formula identity do
not independently verify their recorded verdicts. The upstream 205-cube
re-check is preserved with its original provenance. Cloud execution and
publication were not launched. No license is selected for this checkout.
