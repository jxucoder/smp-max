# Results and evidence

Scientific status: 2026-09-08, as recorded at source commit `30ad2c3`.
The repository reorganization preserves the mathematical statements and
the saved evidence. See [verification](verification.md) to repeat checks.

## Evidence types

- **Kernel-checked theorem:** a Lean statement, with its hypotheses and axioms.
- **Checked certificate:** an UNSAT proof for a specific CNF, checked externally by cake_lpr.
- **Validated computation:** an unformalized program cross-checked against independent methods.

## Result ledger

| Claim | Formal layer | External evidence | Remaining limitation |
|---|---|---|---|
| **f(5) = 16** | `f5_eq_16_of_unsat` combines an upper bound conditional on 120 UNSAT cube formulas with a kernel-checked witness of 16. | All 120 Lean-exported cubes were refuted and checked by cake_lpr. | Certificates are regenerable; only historical verification logs are retained here. Certificate checking remains outside Lean. |
| **f(6) ≤ 48** | `validity_unconditional` reduces arbitrary instances to legal schedules dominating their matching counts. | The completed campaign records 318,736 checked certificates covering all root cubes through their split trees. Independent earlier enumeration also tops out at 48. | The counterexample-to-satisfiable-cube theorem and complete formal coverage assembly remain in progress. |
| **f(6) ≥ 48** | No kernel witness theorem currently included for this order. | Explicit dihedral witness, independently recounted. | Computational lower-bound verification. |
| **f(7) ≥ 85** | No Lean theorem for these witnesses. | Two explicit witnesses; brute-force matching sets, a full blocking-pair recount, and rotation-poset downsets agree. | The upper bound is open. |
| **A344669(3,4,5) = 1092 / 144 / 507,254,400** | Not formalized. | Earlier profile enumeration, including the retained order-5 results. | Historical validated computation. |

Follow the [order-5 guide](f5.md), [order-6 guide](f6.md), and
[order-7 guide](f7.md) for the associated sources and witnesses.

## The order-6 formalization gap

The required implication is:

> Any well-formed order-6 instance with at least 49 stable matchings
> yields a satisfying assignment to a campaign cube.

Refuting every cube then rules out such an instance. The converse alone
(a satisfying assignment gives a large instance) would not justify this
UNSAT upper-bound argument.

Completed pieces include the schedule reduction, variable decoding, legal
schedule length bound, cyclic shapes, and preference-variable/read-off
semantics. The [active proof plan](design/f6-faithfulness.md) records the
remaining normalization, coverage, clause-family, and assembly obligations.
The seven new modules documented in that plan contain 1,803 lines and 131
theorems in the original snapshot; those are dated historical counts.

## Completed order-6 campaign

| Item | Recorded result |
|---|---|
| Root cubes | 25,493 |
| Distinct cubes, including split children | 321,492 |
| Verified certificate records | 318,736 |
| Split parents | 2,756 |
| SAT / missing / bad records in final audit | 0 / 0 / 0 |
| Base formula | 84,882 variables; 2,709,212 clauses |
| Total recorded solver time | 1,076,400 seconds |
| Certificates | Approximately 20 TB generated, checked, then deleted |

The [campaign artifact directory](../results/f6/campaign-2026-09-08/README.md)
contains the immutable journal, original audit outputs, summary, and provenance.
Every verified record stores formula/certificate hashes and checker verdicts.
Hashes identify data; they do not substitute for checking a proof.

The original snapshot compared Lean/Python root and split-child lists and
sampled four per-cube formula hashes. Full Lean re-export of all verified
cubes remains a [roadmap item](roadmap.md). Migration validation is recorded
separately in [layout verification](layout-verification.md).

## Cross-checks and trust boundary

The f(5) result combines Lean's kernel and the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`, the mathematical definitions, the
DIMACS printer, and an external certificate checker. The solver is not
trusted for UNSAT: its proof is checked. The standalone witness needs only
`propext`.

For f(6), the positive control at 48 is satisfiable and decodes to the
dihedral schedule; the corresponding threshold-49 instance is UNSAT.
The earlier exhaustive enumeration evaluated 26,574,282,886 schedule
nodes, with maximum 48. These are supporting computational checks; they
do not close the remaining formalization gap.
