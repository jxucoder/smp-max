# Tools

Run from the repository root. Direct script invocation and `python3 -m`
invocation both resolve repository imports without changing directories.

| Tool | Purpose |
|---|---|
| [verify_witnesses.py](verify_witnesses.py) | Recount all four saved witnesses and compare matching sets, poset counts, and saved schedules |
| [verify_five_cubes.py](verify_five_cubes.py) | Export and certify Lean-defined order-5 cubes; retain failures |
| [check_lean.sh](check_lean.sh) | Build Lean, inspect axioms, and run standalone formal checks |
| [check_artifacts.py](check_artifacts.py) | Check the retained evidence manifest |
| [check_docs.py](check_docs.py) | Check local Markdown file targets |
| [stable_matchings.py](stable_matchings.py) | Brute-force counter over best-first preference lists |
| [direct_encoding.py](direct_encoding.py) | PySAT direct instance encoding |
| [schedule_encoding.py](schedule_encoding.py) | Schedule CNF used by the order-6 campaign |
| [rotation_poset.py](rotation_poset.py) | Independent rank-table counter and lattice/poset analysis |
| [generate_five_witness.py](generate_five_witness.py) | Regenerate the standalone order-5 Lean witness |
| [campaign/](campaign/README.md) | Campaign driver, calibration, merge tools, dashboard, optional Modal backend |

See [verification](../docs/verification.md) for prerequisites and exact
success criteria. The direct encoding requires the optional PySAT dependency;
the other local Python verification tools use the standard library.
