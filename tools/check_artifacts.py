#!/usr/bin/env python3
"""Check all retained evidence files against the published SHA-256 manifest."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / 'results/manifest.json').read_text())
    failures = []
    for entry in manifest['files']:
        path = ROOT / entry['path']
        digest = hashlib.sha256()
        try:
            with path.open('rb') as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b''):
                    digest.update(chunk)
            if digest.hexdigest() != entry['sha256']:
                failures.append(f"Hash mismatch: {entry['path']}")
        except OSError as exc:
            failures.append(str(exc))
    if failures:
        sys.exit('\n'.join(failures))
    print(f"Verified SHA-256 of {len(manifest['files'])} retained artifacts.")


if __name__ == '__main__':
    main()
