#!/usr/bin/env python3
"""Compare the complete recorded campaign with the current Lean exporters.

Checks the base formula, root/split lists, final leaf set and every recorded
formula hash. This checks formula identity, not the deleted certificates.
Build the exporters first with bash tools/check_lean.sh.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.campaign import cube_campaign as campaign


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--journal', type=Path,
                        default=ROOT / 'results/f6/campaign-2026-09-08/campaign.jsonl.gz')
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'runs/f6/lean-identity')
    parser.add_argument('--export-dir', type=Path, default=ROOT / 'lean/.lake/build/bin')
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    journal = args.journal.resolve()
    if journal.suffix == '.gz':
        expanded = out / 'campaign.jsonl'
        with gzip.open(journal, 'rb') as source, expanded.open('wb') as dest:
            shutil.copyfileobj(source, dest)
        journal = expanded
    records, headers = campaign.load_journal(str(journal), with_headers=True)
    require(bool(records) and bool(headers), 'Journal is empty or has no header')
    verified = {c for c, r in records.items() if r['status'] == 'verified'}
    parents = [c for c, r in records.items() if r['status'] == 'split']
    (out / 'all-ids.txt').write_text(''.join(c + '\n' for c in records))
    (out / 'split-ids.txt').write_text(''.join(c + '\n' for c in parents))
    (out / 'verified-ids.txt').write_text(''.join(c + '\n' for c in sorted(verified)))

    def export(exe, filename, *options):
        path = out / filename
        subprocess.run([str(args.export_dir.resolve() / exe), str(path), *options], check=True)
        return path

    subprocess.run([sys.executable, str(ROOT / 'tools/campaign/cube_campaign.py'),
                    '--audit', '--journal', str(journal)], check=True)
    base = export('export_sched_cnf', 'base.cnf')
    digest = hashlib.sha256(base.read_bytes()).hexdigest()
    require(all(h.get('base_sha256') == digest for h in headers), 'Base formula hash differs')
    roots = export('export_cubes6', 'roots.txt').read_text().splitlines()
    expected_roots = [campaign.cube_id(p, c) for p, c in campaign.root_cubes(2)]
    require(roots == expected_roots, 'Root cube lists differ')
    children = export('export_cubes6', 'children.tsv', '--parents=' + str(out / 'split-ids.txt'))
    expected_children = []
    for cid in parents:
        prefix, stopped = campaign.parse_cube_id(cid)
        expected_children.extend(cid + '\t' + campaign.cube_id(p, c)
                                 for p, c in campaign.split_children(prefix, stopped))
    require(children.read_text().splitlines() == expected_children, 'Split children differ')
    final = export('export_cubes6', 'final-ids.txt', '--final').read_text().splitlines()
    require(len(final) == len(set(final)) and set(final) == verified,
            'Lean finalCubes differs from the journal verified set')
    print(f'Identity: {len(roots)} roots, {len(parents)} splits, '
          f'{len(expected_children)} children, {len(final)} final leaves match.', flush=True)
    units = export('export_cubes6', 'units.tsv', '--units=' + str(out / 'all-ids.txt'))
    subprocess.run([sys.executable, str(ROOT / 'tools/campaign/verify_lean_hashes.py'),
                    str(base), str(units), str(journal)], check=True)
    report = dict(base_sha256=digest, roots=len(roots), splits=len(parents),
                  split_children=len(expected_children), final_leaves=len(final),
                  formula_hashes=sum(bool(r.get('cnf_sha256')) for r in records.values()),
                  all_identity_checks_passed=True)
    (out / 'summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print('All Lean campaign identity checks passed. Certificates were not re-solved.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        sys.exit(f'Identity check failed: {exc}')
