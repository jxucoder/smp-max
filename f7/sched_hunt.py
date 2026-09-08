"""Sub-budget size-2 schedule search (the regime the n=7 record actually lives in).

hunt7.py searched only FULL-budget schedules (all C(n,2) transpositions).
The published 81-instance has 18 of 21 rotations, so full budget excludes it
-- exactly the odd-order pattern seen at n=5 (8 of 10).  Here the schedule
length is itself a search variable.

Usage: python3 sched_hunt.py N SEED SECONDS [--full]
  --full   pin the length at C(N,2) and disable grow/shrink moves (the
           full-budget regime of the retired hunt7.py; caps at 80 at n=7)
Without --full the random stream is unchanged from the 2026-09-06 runs
(seeds 9 and 5 regenerate schedules A and B of lb85.txt byte for byte).
"""
import random, sys, time
from itertools import permutations, combinations

N = int(sys.argv[1]); SEED = int(sys.argv[2]); SECS = float(sys.argv[3])
FULL = "--full" in sys.argv[4:]   # full-budget mode: length pinned at C(N,2) (hunt7.py regime)
RMAX = N * (N - 1) // 2
PAIRS = [tuple(p) for p in combinations(range(N), 2)]

PERMS = []
for p in permutations(range(N)):
    inv = [0] * N
    for m in range(N):
        inv[p[m]] = m
    PERMS.append((p, tuple(inv)))


def count_stable(mrank, wrank):
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
    return cnt


def build(seq):
    """Apply the swaps; bottom-complete both sides' unvisited partners."""
    mu = list(range(N))
    mt = [[m] for m in range(N)]
    wt = [[w] for w in range(N)]
    for i, (a, b) in enumerate(seq):
        wa, wb = mu[a], mu[b]
        if wb in mt[a] or wa in mt[b] or b in wt[wa] or a in wt[wb]:
            return None, i
        mu[a], mu[b] = wb, wa
        mt[a].append(wb); mt[b].append(wa)
        wt[wa].append(b); wt[wb].append(a)
    mrank = [[0] * N for _ in range(N)]
    wrank = [[0] * N for _ in range(N)]
    for m in range(N):
        order = mt[m] + [w for w in range(N) if w not in mt[m]]
        for pos, w in enumerate(order):
            mrank[m][w] = pos
    for w in range(N):
        seen = list(reversed(wt[w]))
        order = seen + [m for m in range(N) if m not in seen]
        for pos, m in enumerate(order):
            wrank[w][m] = pos
    return (mrank, wrank), len(seq)


def score(seq):
    inst, i = build(seq)
    return count_stable(*inst) if inst else i - len(seq) - 1


def mutate(seq, rng):
    s = list(seq)
    op = rng.randrange(3) if FULL else rng.randrange(5)
    if op == 0 and len(s) > 1:
        i, j = rng.sample(range(len(s)), 2); s[i], s[j] = s[j], s[i]
    elif op == 1 and len(s) > 1:
        i, j = rng.sample(range(len(s)), 2); s.insert(j, s.pop(i))
    elif op == 2 and len(s) > 1:
        i = rng.randrange(len(s)); s[i] = rng.choice(PAIRS)
    elif op == 3 and len(s) < RMAX:                    # grow
        s.insert(rng.randrange(len(s) + 1), rng.choice(PAIRS))
    elif len(s) > 2:                                    # shrink
        s.pop(rng.randrange(len(s)))
    return s


def main():
    rng = random.Random(SEED)
    t_end = time.time() + SECS
    best, best_seq, evals, restarts = 0, None, 0, 0
    while time.time() < t_end:
        r = RMAX if FULL else rng.randrange(max(3, RMAX - 8), RMAX + 1)
        seq = [rng.choice(PAIRS) for _ in range(r)]
        cur = score(seq); stale = 0
        while stale < 4000 and time.time() < t_end:
            s2 = mutate(seq, rng); c2 = score(s2); evals += 1
            if c2 >= cur:
                if c2 > cur:
                    stale = 0
                    if c2 > best:
                        best, best_seq = c2, list(s2)
                        print(f"[n={N} seed {SEED}] best {c2} len={len(s2)} evals={evals}", flush=True)
                else:
                    stale += 1
                seq, cur = s2, c2
            else:
                stale += 1
        restarts += 1
    print(f"[n={N} seed {SEED}] DONE best={best} evals={evals} restarts={restarts}", flush=True)
    print(f"[n={N} seed {SEED}] best_seq={best_seq}", flush=True)


main()
