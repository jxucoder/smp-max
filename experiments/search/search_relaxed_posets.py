"""Relaxed upper-bound exploration for f(6) in the full-budget regime.

Necessary conditions (verified on the dihedral instance): 15 rotations,
each of size 2 (two men + two women); each of the 6 men and 6 women lies
in exactly 5 rotations, and those 5 form a CHAIN in the rotation poset.
The true poset contains the union of all 12 chain orders, so
  #downsets(true poset) <= #downsets(transitive closure of the chains).

This script searches over labelings (12 chains over 15 rotation ids,
2-regular per side) maximizing downsets of the chain-closure. If the
relaxed maximum is <= 48, the full-budget regime cannot beat the
dihedral instance (modulo the chain lemma). If >= 49, the witnessing
labelings are precise targets for instance hunting.
"""

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
import random
import sys
import time
from functools import lru_cache

P = 15
N = 6


def closure_from_chains(chains):
    """chains: list of ordered id-lists. Return (ok, up) where up[x] =
    bitmask of strict upper bounds of x, or ok=False if cyclic."""
    succ = [0] * P
    for ch in chains:
        for a, b in zip(ch, ch[1:]):
            succ[a] |= 1 << b
    # transitive closure via repeated squaring-ish relaxation
    up = succ[:]
    for _ in range(P):
        changed = False
        for x in range(P):
            new = up[x]
            m = up[x]
            while m:
                b = m & -m
                new |= up[b.bit_length() - 1]
                m ^= b
            if new != up[x]:
                up[x] = new
                changed = True
        if not changed:
            break
    for x in range(P):
        if up[x] >> x & 1:
            return False, None
    return True, up


def count_downsets(up):
    """#downsets of the poset given strict-upper masks (<= 15 elements)."""
    # down[x] = mask of strict lower bounds
    down = [0] * P
    for x in range(P):
        m = up[x]
        while m:
            b = m & -m
            down[b.bit_length() - 1] |= 1 << x
            m ^= b

    memo = {}

    def rec(mask):
        if mask == 0:
            return 1
        if mask in memo:
            return memo[mask]
        x = (mask & -mask).bit_length() - 1
        # if x is minimal in mask, split on x; else pick a minimal element
        while down[x] & mask:
            x = ((down[x] & mask) & -(down[x] & mask)).bit_length() - 1
        without_x = rec(mask & ~(1 << x))
        without_upx = rec(mask & ~((1 << x) | up[x]))
        memo[mask] = without_x + without_upx
        return memo[mask]

    # downsets(P) = downsets(P - x) counts those NOT containing x;
    # those containing x must contain down[x]... simpler standard split:
    # D(P) = D(P \ {x}) + D(P \ up*(x)) with x minimal:
    # (not containing x) + (containing x -> exclude nothing above forced;
    #  remaining freedom is P minus x and everything above x)
    return rec((1 << P) - 1)


def eval_state(man_chains, woman_chains):
    ok, up = closure_from_chains(man_chains + woman_chains)
    if not ok:
        return -1
    return count_downsets(up)


def dihedral_labeling():
    from tools.rotation_poset import extract_rotations
    rows = ["123456", "214365", "365214", "456123", "541632", "632541"]
    d_m = [[int(c) - 1 for c in r] for r in rows]
    d_w = [[6 - int(rows[i][j]) for i in range(6)] for j in range(6)]
    rots, ple = extract_rotations(d_m, d_w)
    assert len(rots) == P
    man_chains, woman_chains = [], []
    for side in (0, 1):
        for x in range(N):
            mine = [a for a in range(P) if x in rots[a][side]]
            mine.sort(key=lambda a: sum(ple[b][a] for b in range(P)))
            (man_chains if side == 0 else woman_chains).append(mine)
    return man_chains, woman_chains


def random_labeling(rng):
    def side():
        ids = list(range(P)) * 2
        rng.shuffle(ids)
        return [ids[i * 5:(i + 1) * 5] for i in range(N)]
    while True:
        mc, wc = side(), side()
        if all(len(set(c)) == 5 for c in mc + wc):
            return mc, wc


def mutate(mc, wc, rng):
    mc = [list(c) for c in mc]
    wc = [list(c) for c in wc]
    tbl = mc if rng.randrange(2) == 0 else wc
    op = rng.randrange(3)
    if op == 0:  # swap adjacent within a chain
        c = tbl[rng.randrange(N)]
        i = rng.randrange(4)
        c[i], c[i + 1] = c[i + 1], c[i]
    elif op == 1:  # swap ids across two chains (keep 2-regularity)
        a, b = rng.sample(range(N), 2)
        i, j = rng.randrange(5), rng.randrange(5)
        if tbl[a][i] not in tbl[b] and tbl[b][j] not in tbl[a]:
            tbl[a][i], tbl[b][j] = tbl[b][j], tbl[a][i]
    else:  # shuffle one chain's order
        c = tbl[rng.randrange(N)]
        rng.shuffle(c)
    return mc, wc


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    minutes = float(sys.argv[2]) if len(sys.argv) > 2 else 30.0
    rng = random.Random(seed)
    t_end = time.time() + minutes * 60

    mc, wc = dihedral_labeling()
    base = eval_state(mc, wc)
    print(f"[seed {seed}] dihedral labeling relaxed downsets = {base}", flush=True)

    best_global = base
    evals = 0
    restarts = 0
    while time.time() < t_end:
        if restarts % 4 == 3:
            mc, wc = random_labeling(rng)
        else:
            mc, wc = dihedral_labeling()
            for _ in range(rng.randrange(0, 6)):
                mc, wc = mutate(mc, wc, rng)
        cur = eval_state(mc, wc)
        stale = 0
        while stale < 3000 and time.time() < t_end:
            m2, w2 = mutate(mc, wc, rng)
            c2 = eval_state(m2, w2)
            evals += 1
            if c2 >= cur and c2 >= 0:
                if c2 > cur:
                    stale = 0
                    if c2 > best_global:
                        best_global = c2
                        print(f"[seed {seed}] relaxed best {c2} "
                              f"(evals {evals}, restart {restarts})", flush=True)
                        if c2 >= 49:
                            print(f"[seed {seed}] TARGET POSET mc={m2} wc={w2}",
                                  flush=True)
                else:
                    stale += 1
                mc, wc, cur = m2, w2, c2
            else:
                stale += 1
        restarts += 1
    print(f"[seed {seed}] done: relaxed best={best_global}, evals={evals}",
          flush=True)


if __name__ == "__main__":
    main()
