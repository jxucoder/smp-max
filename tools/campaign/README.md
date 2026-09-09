# Campaign tools

The [campaign reference](../../docs/reference/campaign.md) documents
setup, working directories, audit semantics, resource needs, and records.

| File | Role |
|---|---|
| [cube_campaign.py](cube_campaign.py) | Run, resume, summarize, or audit an order-6 campaign |
| [calibrate_cubes.py](calibrate_cubes.py) | Explore prefix counts and cube hardness |
| [merge_journals.py](merge_journals.py) | Merge journal attempts before auditing |
| [dashboard.py](dashboard.py) / [dashboard.html](dashboard.html) | Read-only local dashboard |
| [run_modal.py](run_modal.py) | Optional paid cloud backend using the same worker |

New campaign output defaults to ignored `runs/f6/`. Saved evidence is
under [results/f6/](../../results/f6/README.md), separate from these tools.

`check_lean_identity.py` compares the complete journal with current Lean
exports (roots, splits, final leaves and every formula hash).
`verify_lean_hashes.py` is the underlying base-plus-units hash checker.
See the [verification guide](../../docs/verification.md).
