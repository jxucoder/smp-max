# Attic: Lean files kept for the record, not built

Neither file here is imported by `lean/SmpF5/SmpF5.lean` or built by
`lake build`, and nothing in the evidence chain depends on them.
`LratPilot.lean` was the n = 4 pilot: the `k = 11` UNSAT certificate for
f(4) ≤ 10 (CNF from `encode.py`, proof from kissat `--plain` and
drat-trim, both embedded verbatim) imported into Lean through Mathlib's
`lrat_proof` tactic as the theorem `f4_ge11_unsat`. The approach was
abandoned for the external, formally verified checker cake_lpr, which is
what every certificate of the f(5) and f(6) campaigns was checked with;
the order-5 and order-6 theorems take the refutations as a hypothesis
instead of importing them. `DiffTest.lean` is the differential-test
harness that evaluated the order-5 Lean definitions (`WF`, `stableCount`
from `SmpF5.Bridge`) on random instances against the counts of the Python
counter `smp.py`, via `#eval`; it was a development-time sanity check of
the definitions, superseded by the kernel-checked theorems themselves.
