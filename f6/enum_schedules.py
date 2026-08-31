"""Exhaustive enumeration of the full-budget schedule space for f(6).

Objects: sequences of 15 wife-swaps (man-pairs), each man in exactly 5,
applied from the identity matching, no partner revisited. Symmetry
reductions: men are labeled by first appearance; adjacent independent
(man-disjoint) swaps are required to be in lex order (kills commuting
duplicates; may leave some, which is harmless for a max).

Usage:
  probe:  python3 enum_schedules.py probe <depth>
  full:   python3 enum_schedules.py full <shard> <nshards>
          (shards split on the choice at depth 2)
"""
import sys
import time

sys.path.insert(0, ".")
from hillclimb import count_stable

N = 6
FULL = 15


def run(mode, shard=0, nshards=1, probe_depth=15):
    mu = list(range(N))
    deg = [0] * N
    mvis = [1 << mu[m] for m in range(N)]
    wvis = [1 << w for w in range(N)]
    mtraj = [[mu[m]] for m in range(N)]
    wtraj = [[w] for w in range(N)]
    seq = []
    stats = {"nodes": 0, "leaves": 0, "best": 0, "t0": time.time()}
    best_seq = [None]
    shard_counter = [0]

    def leaf_eval():
        mrank = [[0] * N for _ in range(N)]
        wrank = [[0] * N for _ in range(N)]
        for m in range(N):
            lst = mtraj[m] + [w for w in range(N) if not (mvis[m] >> w & 1)]
            for pos, w in enumerate(lst):
                mrank[m][w] = pos
        for w in range(N):
            lst = list(reversed(wtraj[w])) + \
                [x for x in range(N) if not (wvis[w] >> x & 1)]
            for pos, x in enumerate(lst):
                wrank[w][x] = pos
        c = count_stable(mrank, wrank)
        stats["leaves"] += 1
        if c > stats["best"]:
            stats["best"] = c
            best_seq[0] = list(seq)
            print(f"new best {c}: seq={seq}", flush=True)

    def dfs(depth, maxused):
        stats["nodes"] += 1
        if depth == probe_depth:
            if depth == FULL:
                leaf_eval()
            else:
                stats["leaves"] += 1
            return
        extended = False
        prev = seq[-1] if seq else None
        for a in range(N):
            for b in range(a + 1, N):
                newc = (a >= maxused) + (b >= maxused)
                if newc == 1 and not (a == maxused or b == maxused):
                    continue
                if newc == 2 and not (a == maxused and b == maxused + 1):
                    continue
                if deg[a] >= 5 or deg[b] >= 5:
                    continue
                if prev is not None:
                    c, d = prev
                    if a != c and a != d and b != c and b != d:
                        if (c, d) > (a, b):
                            continue
                wa, wb = mu[a], mu[b]
                if (mvis[a] >> wb & 1 or mvis[b] >> wa & 1
                        or wvis[wa] >> b & 1 or wvis[wb] >> a & 1):
                    continue
                if depth == 2 and mode == "full":
                    shard_counter[0] += 1
                    if (shard_counter[0] - 1) % nshards != shard:
                        continue
                # apply
                mu[a], mu[b] = wb, wa
                deg[a] += 1
                deg[b] += 1
                mvis[a] |= 1 << wb
                mvis[b] |= 1 << wa
                wvis[wa] |= 1 << b
                wvis[wb] |= 1 << a
                mtraj[a].append(wb)
                mtraj[b].append(wa)
                wtraj[wa].append(b)
                wtraj[wb].append(a)
                seq.append((a, b))
                extended = True
                dfs(depth + 1, max(maxused, b + 1))
                seq.pop()
                mtraj[a].pop()
                mtraj[b].pop()
                wtraj[wa].pop()
                wtraj[wb].pop()
                mvis[a] &= ~(1 << wb)
                mvis[b] &= ~(1 << wa)
                wvis[wa] &= ~(1 << b)
                wvis[wb] &= ~(1 << a)
                deg[a] -= 1
                deg[b] -= 1
                mu[a], mu[b] = wa, wb
        if not extended and depth < probe_depth:
            leaf_eval()

    dfs(0, 0)
    dt = time.time() - stats["t0"]
    print(f"mode={mode} shard={shard}/{nshards} depth={probe_depth}: "
          f"nodes={stats['nodes']}, leaves={stats['leaves']}, "
          f"best={stats['best']}, {dt:.1f}s", flush=True)


if __name__ == "__main__":
    if sys.argv[1] == "probe":
        run("probe", probe_depth=int(sys.argv[2]))
    else:
        run("full", shard=int(sys.argv[2]), nshards=int(sys.argv[3]))
