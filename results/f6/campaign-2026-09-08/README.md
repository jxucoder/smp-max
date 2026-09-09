# Completed order-6 campaign, 2026-09-08

This directory preserves the campaign snapshot from source commit `30ad2c3`.
The journal and historical logs are unchanged. Original paths and source
hashes in records deliberately describe the run that produced them.

| File | Meaning |
|---|---|
| [campaign.jsonl.gz](campaign.jsonl.gz) | Complete append-only record snapshot; approximately 464 MB decompressed |
| [audit-complete.txt](audit-complete.txt) | Original final audit after the remaining cases were retried |
| [audit-before-retries.txt](audit-before-retries.txt) | Earlier main-run audit; not the final completion verdict |
| [summary.json](summary.json) | Dimensions, counts, base formula identity, and original header records |
| [campaign.log](campaign.log) | Original full run output |
| [driver-command.txt](driver-command.txt) | Historical command snapshot, not a current launch recipe |

The remaining `dryrun`, `fixcheck`, `cadical_check`, `cadical_hard`, and
`depth3_probe` files are earlier subsets and probes; their journals do not
individually cover the completed campaign. The [development history](../../../docs/history/f6-campaign-development.md)
explains them.

Final recorded coverage: 25,493 roots, 321,492 distinct cubes, 318,736
verified records, and 2,756 split parents; zero SAT, missing, or bad cases.
The original certificates (about 20 TB total) were deleted after checking.
Their hashes remain in the journal; independently rechecking certificates
requires regeneration. The [current reference](../../../docs/reference/campaign.md)
provides commands and resource expectations.

All retained bytes are listed in the [artifact manifest](../../manifest.json).
The [layout validation](../../../docs/layout-verification.md) records checks
of the renamed implementation against this evidence.
