#!/usr/bin/env python3
"""Export and certify the 120 Lean-defined order-5 upper-bound cubes.

Expected UNSAT exit 20 is handled explicitly. Any missing/failed checker
verdict stops the run and retains its artifacts. Successful proofs are
deleted only after their hashes and checker outcomes have been recorded.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def executable(value):
    found = shutil.which(str(value))
    if found is None:
        raise ValueError(f'Executable not found: {value}')
    return str(Path(found).resolve())


def run_stage(command, log, expected_rc, verdict=None):
    with log.open('w') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    output = log.read_text(errors='replace')
    if result.returncode != expected_rc or (verdict and verdict not in output.splitlines()):
        raise ValueError(f'{command[0]} failed (exit {result.returncode}); see {log}. Artifacts retained.')
    return result.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'runs/f5/lean-cubes')
    parser.add_argument('--exporter', default=str(ROOT / 'lean/.lake/build/bin/export_cnf'))
    parser.add_argument('--kissat', default='kissat')
    parser.add_argument('--drat-trim', default=str(ROOT / 'dt-src/drat-trim'))
    parser.add_argument('--cake-lpr', default=str(ROOT / 'cake_lpr-src/cake_lpr'))
    parser.add_argument('--export-only', action='store_true')
    parser.add_argument('--keep-proofs', action='store_true')
    parser.add_argument('--cubes', nargs='+', type=int, help='subset of cube indices 0..119; default all 120')
    args = parser.parse_args()
    cubes = list(range(120)) if args.cubes is None else args.cubes
    if len(set(cubes)) != len(cubes) or any(i < 0 or i >= 120 for i in cubes):
        raise ValueError('Cube indices must be distinct integers from 0 to 119')
    exporter = executable(args.exporter)
    if not args.export_only:
        kissat, trim, cake = map(executable, [args.kissat, args.drat_trim, args.cake_lpr])
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    subprocess.run([exporter], cwd=out, check=True)
    expected = [out / f'cubeL{i:03d}.cnf' for i in range(120)]
    if not all(p.is_file() for p in expected):
        raise ValueError('Exporter did not produce all 120 upper-bound cubes')
    if args.export_only:
        print(f'Exported 120 upper-bound cubes and their positive controls to {out}')
        return
    with (out / 'verification.jsonl').open('a') as journal:
        for i in cubes:
            stem = out / f'cubeL{i:03d}'
            cnf, drat, lrat = [stem.with_suffix(ext) for ext in ['.cnf', '.drat', '.lrat']]
            cnf_sha = digest(cnf)
            solver_rc = run_stage([kissat, '-q', str(cnf), str(drat)], stem.with_suffix('.kissat.log'), 20)
            trim_rc = run_stage([trim, str(cnf), str(drat), '-L', str(lrat)], stem.with_suffix('.drat-trim.log'), 0, 's VERIFIED')
            lrat_sha = digest(lrat)
            cake_rc = run_stage([cake, str(cnf), str(lrat)], stem.with_suffix('.cake-lpr.log'), 0, 's VERIFIED UNSAT')
            journal.write(json.dumps(dict(cube=f'cubeL{i:03d}', cnf_sha256=cnf_sha, lrat_sha256=lrat_sha,
                                          solver_rc=solver_rc, drat_trim_rc=trim_rc, cake_rc=cake_rc,
                                          verdict='s VERIFIED UNSAT', solver=kissat, checker=cake)) + '\n')
            journal.flush()
            if not args.keep_proofs:
                drat.unlink()
                lrat.unlink()
            print(f'cubeL{i:03d}: VERIFIED UNSAT', flush=True)
    print(f'Verified {len(cubes)}/120 cubes in this run.' + (' All upper-bound cubes checked.' if len(cubes) == 120 else ' This subset alone does not establish the upper bound.'))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        sys.exit(f'Verification failed: {exc}')
