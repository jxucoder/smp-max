"""Generalized schedule enumeration for f(6): rotations of any size >= 2.

A step is a directed cycle (m0,...,mk-1): man mi's new wife = current
wife of m(i+1). Budget: total moved-man slots <= 30, each man <= 5 moves.
EVERY valid node is evaluated (partial schedules = instances with partial
trajectories, bottom-completed), covering all sub-budget regimes.

By the bridge lemma (any instance's count <= its schedule's read-off
count), the maximum over this enumeration upper-bounds f(6).

Symmetry: conservative — first step must contain man 0 and be in a fixed
canonical rotation; adjacent man-disjoint steps must be lex-ordered.
(Weaker than full canonicalization: duplicates possible, misses none.)

Usage: python3 -m experiments.enumeration.enumerate_cycle_schedules <probe_budget|full> [shard nshards]
"""

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import sys
import time
from itertools import combinations, permutations
from experiments.search.search_instances import count_stable

N = 6
BUDGET = 30


def all_steps():
    steps = []
    for k in range(2, N + 1):
        for sub in combinations(range(N), k):
            first = sub[0]
            for rest in permutations(sub[1:]):
                steps.append((first,) + rest)
    return steps


STEPS = all_steps()


def run(budget_cap, shard=0, nshards=1):
    mu = list(range(N))
    moves_used = [0] * N
    mvis = [1 << m for m in range(N)]
    wvis = [1 << w for w in range(N)]
    mtraj = [[m] for m in range(N)]
    wtraj = [[w] for w in range(N)]
    seq = []
    stats = {"nodes": 0, "best": 0, "t0": time.time()}
    shard_ctr = [0]

    def evaluate():
        mr = [[0] * N for _ in range(N)]
        wr = [[0] * N for _ in range(N)]
        for m in range(N):
            lst = mtraj[m] + [w for w in range(N) if not (mvis[m] >> w & 1)]
            for pos, w in enumerate(lst):
                mr[m][w] = pos
        for w in range(N):
            lst = list(reversed(wtraj[w])) + \
                [m for m in range(N) if not (wvis[w] >> m & 1)]
            for pos, m in enumerate(lst):
                wr[w][m] = pos
        c = count_stable(mr, wr)
        if c > stats["best"]:
            stats["best"] = c
            print(f"new best {c}: seq={seq}", flush=True)

    def dfs(used):
        stats["nodes"] += 1
        extended = False
        prev = seq[-1] if seq else None
        for st in STEPS:
            k = len(st)
            if used + k > budget_cap:
                continue
            if not seq and 0 not in st:
                continue
            if any(moves_used[m] >= 5 for m in st):
                continue
            if prev is not None:
                pset = set(prev)
                if pset.isdisjoint(st) and prev > st:
                    continue
            # validity: mi gets wife of m(i+1)
            newwife = {st[i]: mu[st[(i + 1) % k]] for i in range(k)}
            ok = True
            for m, w in newwife.items():
                if mvis[m] >> w & 1 or wvis[w] >> m & 1:
                    ok = False
                    break
            if not ok:
                continue
            if len(seq) == 1 and nshards > 1:
                shard_ctr[0] += 1
                if (shard_ctr[0] - 1) % nshards != shard:
                    continue
            # apply
            oldwife = {m: mu[m] for m in st}
            for m, w in newwife.items():
                mu[m] = w
                moves_used[m] += 1
                mvis[m] |= 1 << w
                wvis[w] |= 1 << m
                mtraj[m].append(w)
                wtraj[w].append(m)
            seq.append(st)
            extended = True
            dfs(used + k)
            seq.pop()
            for m, w in newwife.items():
                mtraj[m].pop()
                wtraj[w].pop()
                mvis[m] &= ~(1 << w)
                wvis[w] &= ~(1 << m)
                moves_used[m] -= 1
                mu[m] = oldwife[m]
        if not extended:
            stats["leaves"] = stats.get("leaves", 0) + 1
            evaluate()

    dfs(0)
    dt = time.time() - stats["t0"]
    print(f"budget={budget_cap} shard={shard}/{nshards}: "
          f"nodes={stats['nodes']}, maximal-leaves={stats.get('leaves', 0)}, "
          f"best={stats['best']}, {dt:.1f}s", flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "full":
        run(BUDGET, int(sys.argv[2]), int(sys.argv[3]))
    else:
        run(int(sys.argv[1]))
