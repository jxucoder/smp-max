# Contributing

Start with the [evidence ledger](docs/results.md) and [roadmap](docs/roadmap.md).
The [architecture guide](docs/architecture.md) and [Lean map](lean/README.md)
explain how the mathematical and computational layers connect.

## Setup

Use Python 3.9 or later. Core witness/campaign tools use the standard
library. Install Lean through elan, then from the repository root:

```bash
(cd lean && lake exe cache get)
python3 tools/verify_witnesses.py
```

Only the direct SAT experiments require PySAT. In an isolated environment:

```bash
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements-experiments.txt
```

The pinned Lean/Mathlib revisions are in `lean/lean-toolchain` and
`lean/lake-manifest.json`. External solver/checker details are in the
[verification guide](docs/verification.md). A C compiler is needed for the
[general enumerator](experiments/README.md).

## Checks appropriate to a change

| Change | Required checks |
|---|---|
| Documentation | `python3 tools/check_docs.py`; execute changed short examples |
| Witness data or counters | `python3 tools/verify_witnesses.py` |
| Retained evidence inventory | `python3 tools/check_artifacts.py`; preserve existing artifact bytes |
| Lean modules or imports | `bash tools/check_lean.sh` |
| Encoder or exporter | Check formula hashes, cube IDs, and Lean/Python identity; changing the formula starts a different evidence chain |
| Campaign coverage or record handling | Audit the saved journal and compare root/split-child sets |
| Certificate runner | `python3 -m unittest discover -s tests`; these check failure handling with fake subprocesses, not mathematical certificates |

The order-6 proof is complete. Its [design record](docs/design/f6-faithfulness.md)
explains the construction; current work is listed in the [roadmap](docs/roadmap.md).
Keep theorem hypotheses visible and preserve the distinction between a
kernel theorem, an external certificate check, and a validated computation.

## Files, experiments, and provenance

Use descriptive Python `snake_case` names, Lean `PascalCase` modules, and
`kebab-case` documentation names. Shared tooling lives in `tools/`; optional
searches and earlier approaches live in `experiments/`. New runs write to
ignored `runs/` directories rather than completed `results/` directories.

For a saved result, record the producing commit, exact command, seed and
configuration, toolchain versions, expected output, and checksums. Preserve
completed journals, cube identifiers, and historical provenance fields.
Use the [format reference](docs/reference/formats.md) for preference data.

Keep current status in `docs/results.md`, remaining tasks in `docs/roadmap.md`,
and dated narratives in `docs/history/`. Use relative Markdown links.
Update the paired PDF if a manuscript's TeX content changes.

No license has been selected. Citation metadata is in [CITATION.cff](CITATION.cff).
