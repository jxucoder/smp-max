# Remaining work

This is the current work list. Established results and evidence belong in
the [ledger](results.md); dated attempts belong in [history](history/README.md).

1. **Complete order-6 faithfulness and coverage.** Finish schedule-level
   normalization, canonical cube coverage including recorded splits,
   clause-family satisfaction, and the final upper-bound assembly.
   The [technical plan](design/f6-faithfulness.md) preserves the precise obligations.
2. **Represent the final split decisions in Lean.** Connect the 2,756 recorded
   split parents to the exact leaf cube set quantified over by the theorem.
3. **Compare every verified cube with Lean exports.** The base formula,
   complete root/split-child lists, and sampled cubes have been checked;
   a full check of 318,736 exported cube files is separate work.
4. **Prepare a citable evidence release.** Decide a license, archive
   regenerable order-5 certificates and the order-6 journal with persistent
   identifiers, update the manuscript drafts, then decide publication and
   submissions. The repository remains unlicensed by the owner's choice.
5. **Develop larger odd-order lower bounds.** Investigate variable-length
   swap schedules at orders 9–15 and the size-2 extremality conjecture.
   A more scalable rotation extractor is needed beyond the current factorial
   matching enumeration. See the [order-7 guide](f7.md).

No remaining proof obligation is discharged by reorganizing files or
improving the documentation. The [layout validation](layout-verification.md)
records preservation checks for that change alone.
