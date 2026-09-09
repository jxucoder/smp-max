# Saved evidence

Completed records are retained separately from source and live runs.
The [manifest](manifest.json) records original paths, source commit,
SHA-256 values, and sizes for the retained evidence and manuscript files.

```bash
python3 tools/check_artifacts.py
```

Run this from the repository root. It checks byte identity, not mathematical
validity. Follow [verification](../docs/verification.md) for independent checks.

| Directory | Contents |
|---|---|
| [f4/](f4/README.md) | Direct-encoding sanity-check CNF |
| [f5/](f5/README.md) | Extremal witness, Lean-cube verification log, earlier direct SAT results and profile enumeration |
| [f6/](f6/README.md) | Dihedral witness, completed certificate campaign, general enumeration, earlier searches |
| [f7/](f7/README.md) | Two 85-matching witnesses and their original source tables |

New computations belong in ignored `runs/` directories. Preserve completed
journals and provenance fields even when paths or source names change.
The structured witness JSON files are derived from the retained original
instances and checked by the witness verifier.
