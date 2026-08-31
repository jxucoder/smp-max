"""Structure-space hunter for f(6) >= 49.

Full-budget regime: 15 size-2 rotations = a sequence of wife-swaps
between pairs of men, each man in exactly 5 swaps (edge multiset =
5-regular on 6 vertices; K6 in the simple case). Starting from the
identity matching, applying the swaps in order yields each man's wife
trajectory and each woman's husband trajectory; if no one revisits a
partner, the preference lists READ OFF the trajectories (men decline,
women improve) and the instance's true stable-matching count is computed
exactly. The dihedral 48-instance is the round-robin schedule in this
space. Search: reorder the sequence / re-pair edges, maximize the count.
"""
import random
import sys
import time
from itertools import combinations

sys.path.insert(0, ".")
from hillclimb import count_stable  # N=6 exact counter

N = 6


def build_instance(seq):
    """seq: list of 15 man-pairs. Returns ((mrank, wrank), 15) on success,
    or (None, k) where k = number of swaps applied before failure."""
    mu = list(range(N))
    mtraj = [[mu[m]] for m in range(N)]
    wtraj = [[w] for w in range(N)]
    for k, (a, b) in enumerate(seq):
        wa, wb = mu[a], mu[b]
        if (wb in mtraj[a] or wa in mtraj[b] or b in wtraj[wa]
                or a in wtraj[wb]):
            return None, k
        mu[a], mu[b] = wb, wa
        mtraj[a].append(wb)
        mtraj[b].append(wa)
        wtraj[wa].append(b)
        wtraj[wb].append(a)
    mrank = [[0] * N for _ in range(N)]
    wrank = [[0] * N for _ in range(N)]
    for m in range(N):
        for pos, w in enumerate(mtraj[m]):
            mrank[m][w] = pos
    for w in range(N):
        for pos, m in enumerate(reversed(wtraj[w])):
            wrank[w][m] = pos
    return (mrank, wrank), 15


def score(seq):
    inst, k = build_instance(seq)
    if inst is None:
        return k - 15          # in [-15, -1): gradient toward validity
    return count_stable(*inst)


def dihedral_seq():
    """The dihedral 48-instance's actual rotation sequence (a topological
    order of its extracted rotation poset), relabeled so that the
    man-optimal matching is the identity."""
    from rotation_poset import extract_rotations, stable_matchings
    rows = ["123456", "214365", "365214", "456123", "541632", "632541"]
    d_m = [[int(c) - 1 for c in r] for r in rows]
    d_w = [[6 - int(rows[i][j]) for i in range(6)] for j in range(6)]
    rots, ple = extract_rotations(d_m, d_w)
    # topological order by number of predecessors
    order = sorted(range(len(rots)), key=lambda a: sum(ple[b][a] for b in range(len(rots))))
    return [tuple(rots[a][0]) for a in order]


def mutate(seq, rng):
    seq = list(seq)
    op = rng.randrange(3)
    if op == 0:  # swap two positions in the order
        i, j = rng.sample(range(15), 2)
        seq[i], seq[j] = seq[j], seq[i]
    elif op == 1:  # move a rotation to a new position
        i, j = rng.sample(range(15), 2)
        x = seq.pop(i)
        seq.insert(j, x)
    else:  # re-pair: swap one endpoint between two rotations (keep degrees)
        i, j = rng.sample(range(15), 2)
        (a, b), (c, d) = seq[i], seq[j]
        if rng.randrange(2):
            na, nc = (a, d), (c, b)
        else:
            na, nc = (a, c), (b, d)
        if na[0] != na[1] and nc[0] != nc[1]:
            seq[i] = tuple(sorted(na))
            seq[j] = tuple(sorted(nc))
    return seq


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    minutes = float(sys.argv[2]) if len(sys.argv) > 2 else 60.0
    rng = random.Random(seed)
    t_end = time.time() + minutes * 60

    rr = dihedral_seq()
    base = score(rr)
    print(f"[seed {seed}] dihedral-seq score = {base} (expect 48)", flush=True)

    best_global = base
    evals = valid = 0
    restarts = 0
    while time.time() < t_end:
        seq = list(rr)
        for _ in range(rng.randrange(0, 10)):
            seq = mutate(seq, rng)
        cur = score(seq)
        stale = 0
        while stale < 5000 and time.time() < t_end:
            s2 = mutate(seq, rng)
            c2 = score(s2)
            evals += 1
            if c2 >= 0:
                valid += 1
            if c2 >= cur:
                if c2 > cur:
                    stale = 0
                    if c2 > best_global:
                        best_global = c2
                        print(f"[seed {seed}] best {c2} (evals {evals}, "
                              f"restart {restarts})", flush=True)
                        if c2 >= 49:
                            print(f"[seed {seed}] *** COUNTEREXAMPLE seq={s2} "
                                  f"inst={build_instance(s2)}", flush=True)
                            return
                else:
                    stale += 1
                seq, cur = s2, c2
            else:
                stale += 1
        restarts += 1
    print(f"[seed {seed}] done: best={best_global}, evals={evals}, "
          f"valid={valid}, restarts={restarts}", flush=True)


if __name__ == "__main__":
    main()
