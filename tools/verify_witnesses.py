#!/usr/bin/env python3
"""Verify saved witnesses with independent matching and rotation-poset counts."""
import argparse
import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import stable_matchings as brute
from tools import rotation_poset


def all_pairs_matchings(mrank, wrank):
    """Test every blocking pair without the early-exit counter's pruning."""
    n = len(mrank)
    matches = set()
    for matching in itertools.permutations(range(n)):
        inverse = [matching.index(w) for w in range(n)]
        blocking = sum(
            mrank[m][w] < mrank[m][matching[m]]
            and wrank[w][m] < wrank[w][inverse[w]]
            for m in range(n) for w in range(n)
        )
        if blocking == 0:
            matches.add(matching)
    return matches


def verify(witness):
    n = witness['order']
    expected = witness['expected_count']
    mp, wp = witness['men_preferences'], witness['women_preferences']
    if len(mp) != n or len(wp) != n or any(
        sorted(row) != list(range(n)) for row in mp + wp
    ):
        raise ValueError(f"{witness['id']}: invalid preference permutations")
    mr, wr = brute.ranks(mp), brute.ranks(wp)
    matches = set(brute.stable_matchings(mp, wp))
    naive = all_pairs_matchings(mr, wr)
    lattice = rotation_poset.stable_matchings(mr, wr)
    _, order = rotation_poset.poset_of_lattice(lattice, mr)
    downsets = rotation_poset.count_downsets(order)
    if matches != naive or matches != set(lattice) or len(matches) != expected or downsets != expected:
        raise ValueError(
            f"{witness['id']}: expected {expected}; brute={len(matches)}, "
            f"all-pairs={len(naive)}, downsets={downsets}; matching sets must also agree"
        )
    if 'schedule' in witness:
        from tools.campaign.cube_campaign import readoff_ranks
        sm, sw = readoff_ranks(n, witness['schedule'])
        if sm != mr or sw != wr:
            raise ValueError(f"{witness['id']}: saved schedule and preference lists disagree")
    print(f"{witness['id']}: {expected} stable matchings; all three counts agree [OK]", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='*', type=Path, help='witness JSON files; defaults to all four saved witnesses')
    args = parser.parse_args()
    paths = args.files or [ROOT / 'results/f5/witness-16.json', ROOT / 'results/f6/witness-48.json', ROOT / 'results/f7/witnesses-85.json']
    total = 0
    for path in paths:
        data = json.loads(path.read_text())
        if data['format_version'] != 1 or not data['witnesses']:
            raise ValueError(f'{path}: expected format version 1 and at least one witness')
        for witness in data['witnesses']:
            verify(witness)
            total += 1
    print(f'Verified {total} witnesses.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError) as exc:
        sys.exit(f'Verification failed: {exc}')
