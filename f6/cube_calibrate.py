#!/usr/bin/env python3
"""Calibrate the order-6 cube campaign: per-cube solve cost distribution.

Loads the k=49 formula once into CaDiCaL and solves a sample of
canonical depth-2 cubes via assumptions (S[0]=s1, S[1]=s2), each under
a conflict budget. Emits one line per cube; summary at the end.

Usage: python3 cube_calibrate.py [sample_size] [conf_budget] [seed]
"""
import itertools, random, sys, time

sys.path.insert(0, ".")
from sched_sat import build, cyclic_shapes

N = 6
BUDGET = N * (N - 1)
PERMAN = N - 1


def canonical_depth2():
    STEPS = cyclic_shapes(N)
    out = []

    def ok_step(matching, tm, tw, used, sched, st):
        k = len(st)
        newmen = [m for m in st if m not in used]
        nxt = list(range(len(used), len(used) + len(newmen)))
        if sorted(newmen) != nxt:
            return None
        newm = list(matching)
        for i, m in enumerate(st):
            w = matching[st[(i + 1) % k]]
            if len(tm[m]) - 1 >= PERMAN or w in tm[m] or m in tw[w]:
                return None
            newm[m] = w
        for prev in reversed(sched):
            if set(prev) & set(st):
                break
            if st < prev:
                return None
        return newm

    id0 = list(range(N))
    tm0 = [[m] for m in range(N)]
    tw0 = [[w] for w in range(N)]
    for s1 in STEPS:
        m1 = ok_step(id0, tm0, tw0, set(), [], s1)
        if m1 is None:
            continue
        tm1 = [list(t) for t in tm0]
        tw1 = [list(t) for t in tw0]
        for i, m in enumerate(s1):
            w = id0[s1[(i + 1) % len(s1)]]
            tm1[m].append(w)
            tw1[w].append(m)
        used1 = set(s1)
        for s2 in STEPS:
            if len(s1) + len(s2) > BUDGET:
                continue
            if ok_step(m1, tm1, tw1, used1, [s1], s2) is not None:
                out.append((s1, s2))
    return out


def main():
    sample_size = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    conf_budget = int(sys.argv[2]) if len(sys.argv) > 2 else 300_000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0

    cubes = canonical_depth2()
    print(f"canonical depth-2 cubes: {len(cubes)}", flush=True)

    rng = random.Random(seed)
    sample = rng.sample(cubes, sample_size)
    # known-hard family: pairs of disjoint transpositions (round-robin-like)
    hard = [c for c in cubes
            if len(c[0]) == 2 and len(c[1]) == 2 and not set(c[0]) & set(c[1])]
    print(f"disjoint-transposition (hard-family) cubes: {len(hard)}", flush=True)
    tagged = [("rand", c) for c in sample] + \
             [("hard", c) for c in rng.sample(hard, min(8, len(hard)))]

    e, hooks = build(N, 49)
    M, V, S, Y, SH, F, P = hooks
    from pysat.solvers import Cadical195
    t0 = time.time()
    solver = Cadical195(bootstrap_with=e.clauses)
    print(f"formula loaded: {e.n} vars {len(e.clauses)} clauses "
          f"in {time.time()-t0:.1f}s", flush=True)

    stats = {"UNSAT": [], "SAT": [], "UNKNOWN": []}
    for tag, (s1, s2) in tagged:
        a = [S[0][SH.index(s1) + 1], S[1][SH.index(s2) + 1]]
        solver.conf_budget(conf_budget)
        t1 = time.time()
        r = solver.solve_limited(assumptions=a)
        dt = time.time() - t1
        status = "UNKNOWN" if r is None else ("SAT" if r else "UNSAT")
        stats[status].append(dt)
        print(f"{tag} {s1}+{s2}: {status} {dt:.2f}s", flush=True)

    for k2, v in stats.items():
        if v:
            v = sorted(v)
            print(f"{k2}: n={len(v)} median={v[len(v)//2]:.2f}s "
                  f"max={v[-1]:.2f}s total={sum(v):.1f}s", flush=True)


if __name__ == "__main__":
    main()
