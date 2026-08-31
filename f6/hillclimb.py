"""Local search for a 6x6 instance with >= 49 stable matchings.

Objective: disprove f(6)=48 (OEIS A357271's conjecture) by exhibiting a
counterexample. Latin instances are exhausted at 48 (A351413), so any
49+ instance is non-Latin: we hill-climb with plateau random walks from
the dihedral 48-instance and random restarts, mutating by swapping two
adjacent entries in one person's preference order.

Counting is exact (all 720 matchings, early-exit stability check).
Improvements >= 48 are logged with the full instance.
"""
import random
import sys
import time
from itertools import permutations

N = 6
PERMS = [(p, tuple(inv := sorted(range(N), key=lambda m: p[m]))) for p in permutations(range(N))]
PERMS = []
for p in permutations(range(N)):
    inv = [0] * N
    for m in range(N):
        inv[p[m]] = m
    PERMS.append((p, tuple(inv)))


def count_stable(mrank, wrank, cutoff=10**9):
    cnt = 0
    for mu, inv in PERMS:
        ok = True
        for m in range(N):
            rm = mrank[m]
            thr = rm[mu[m]]
            if thr:
                for w in range(N):
                    if rm[w] < thr and wrank[w][m] < wrank[w][inv[w]]:
                        ok = False
                        break
                if not ok:
                    break
        if ok:
            cnt += 1
            if cnt >= cutoff:
                return cnt
    return cnt


def ranks_to_order(row):
    return sorted(range(N), key=lambda x: row[x])


def order_to_ranks(order):
    r = [0] * N
    for pos, x in enumerate(order):
        r[x] = pos
    return r


def dihedral48():
    rows = ["123456", "214365", "365214", "456123", "541632", "632541"]
    mrank = [[int(c) - 1 for c in r] for r in rows]
    wrank = [[6 - int(rows[i][j]) for i in range(N)] for j in range(N)]
    return mrank, wrank


def random_instance(rng):
    return ([rng.sample(range(N), N) for _ in range(N)],
            [rng.sample(range(N), N) for _ in range(N)])


def mutate(mrank, wrank, rng):
    side = rng.randrange(2)
    i = rng.randrange(N)
    pos = rng.randrange(N - 1)
    tbl = mrank if side == 0 else wrank
    order = ranks_to_order(tbl[i])
    order[pos], order[pos + 1] = order[pos + 1], order[pos]
    new_row = order_to_ranks(order)
    new_tbl = list(tbl)
    new_tbl[i] = new_row
    return (new_tbl, wrank) if side == 0 else (mrank, new_tbl)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    minutes = float(sys.argv[2]) if len(sys.argv) > 2 else 60.0
    rng = random.Random(seed)
    t_end = time.time() + minutes * 60
    best_global = 0
    evals = 0
    restarts = 0
    while time.time() < t_end:
        # seed schedule: dihedral + noise, or random
        if restarts % 3 != 2:
            mrank, wrank = dihedral48()
            for _ in range(rng.randrange(0, 8)):
                mrank, wrank = mutate(mrank, wrank, rng)
        else:
            mrank, wrank = random_instance(rng)
        cur = count_stable(mrank, wrank)
        stale = 0
        while stale < 4000 and time.time() < t_end:
            m2, w2 = mutate(mrank, wrank, rng)
            c2 = count_stable(m2, w2)
            evals += 1
            if c2 >= cur:
                if c2 > cur:
                    stale = 0
                    if c2 > best_global:
                        best_global = c2
                        print(f"[seed {seed}] new best {c2} after {evals} evals "
                              f"(restart {restarts})", flush=True)
                        if c2 >= 48:
                            print(f"[seed {seed}] mrank={m2} wrank={w2}", flush=True)
                        if c2 >= 49:
                            print(f"[seed {seed}] *** CONJECTURE COUNTEREXAMPLE ***", flush=True)
                            return
                else:
                    stale += 1
                mrank, wrank, cur = m2, w2, c2
            else:
                stale += 1
        restarts += 1
    print(f"[seed {seed}] done: best={best_global}, evals={evals}, restarts={restarts}", flush=True)


if __name__ == "__main__":
    main()
