"""Rotation-poset microscope.

For an instance, the stable matchings under the man-dominance order form
a distributive lattice; by Birkhoff it is the lattice of downsets of the
poset P of its join-irreducible elements (equivalently, the rotation
poset). This script extracts P, verifies #downsets(P) = #matchings, and
prints structural invariants (size, height, width, cover relations).
"""
import sys
from itertools import permutations


def stable_matchings(mrank, wrank):
    n = len(mrank)
    out = []
    for mu in permutations(range(n)):
        inv = [0] * n
        for m in range(n):
            inv[mu[m]] = m
        ok = True
        for m in range(n):
            rm = mrank[m]
            thr = rm[mu[m]]
            if thr:
                for w in range(n):
                    if rm[w] < thr and wrank[w][m] < wrank[w][inv[w]]:
                        ok = False
                        break
                if not ok:
                    break
        if ok:
            out.append(mu)
    return out


def poset_of_lattice(matchings, mrank):
    n = len(mrank)
    S = matchings
    k = len(S)
    # man-dominance: mu <= nu iff every man weakly prefers mu
    le = [[all(mrank[m][S[i][m]] <= mrank[m][S[j][m]] for m in range(n))
           for j in range(k)] for i in range(k)]
    # covers: i < j with nothing between
    covers = [[le[i][j] and i != j and not any(
        le[i][t] and le[t][j] and t != i and t != j for t in range(k))
        for j in range(k)] for i in range(k)]
    # join-irreducible: covers exactly one element
    irr = [j for j in range(k) if sum(covers[i][j] for i in range(k)) == 1]
    # induced order on irreducibles
    p = len(irr)
    ple = [[le[irr[a]][irr[b]] for b in range(p)] for a in range(p)]
    return irr, ple


def count_downsets(ple):
    p = len(ple)
    total = 0
    for mask in range(1 << p):
        ok = True
        for b in range(p):
            if mask >> b & 1:
                for a in range(p):
                    if ple[a][b] and not (mask >> a & 1):
                        ok = False
                        break
                if not ok:
                    break
        total += ok
    return total


def describe(name, mrank, wrank):
    S = stable_matchings(mrank, wrank)
    irr, ple = poset_of_lattice(S, mrank)
    p = len(irr)
    ds = count_downsets(ple)
    strict = [[ple[a][b] and a != b for b in range(p)] for a in range(p)]
    covers = [[strict[a][b] and not any(strict[a][t] and strict[t][b]
              for t in range(p)) for b in range(p)] for a in range(p)]
    ncov = sum(map(sum, covers))
    # height = longest chain, width = largest antichain (brute force ok, p small)
    import functools
    @functools.lru_cache(None)
    def h(a):
        succs = [b for b in range(p) if covers[a][b]]
        return 1 + max((h(b) for b in succs), default=0)
    height = max((h(a) for a in range(p)), default=0)
    width = 0
    for mask in range(1 << p):
        els = [i for i in range(p) if mask >> i & 1]
        if all(not strict[a][b] and not strict[b][a]
               for i, a in enumerate(els) for b in els[i + 1:]):
            width = max(width, len(els))
    print(f"{name}: |matchings|={len(S)}, poset size={p}, downsets={ds} "
          f"{'OK' if ds == len(S) else 'MISMATCH!'}, covers={ncov}, "
          f"height={height}, width={width}")
    rel = [(a, b) for a in range(p) for b in range(p) if covers[a][b]]
    print(f"  cover relations: {rel}")


if __name__ == "__main__":
    witness_m = [[2, 0, 1, 4, 3], [1, 3, 4, 2, 0], [2, 4, 3, 0, 1], [4, 1, 0, 2, 3], [0, 2, 3, 4, 1]]
    witness_w = [[1, 3, 2, 0, 4], [4, 1, 0, 3, 2], [2, 0, 1, 4, 3], [1, 2, 3, 4, 0], [0, 4, 3, 1, 2]]
    describe("n=5 witness (16)", witness_m, witness_w)

    rows = ["123456", "214365", "365214", "456123", "541632", "632541"]
    d_m = [[int(c) - 1 for c in r] for r in rows]
    d_w = [[6 - int(rows[i][j]) for i in range(6)] for j in range(6)]
    describe("n=6 dihedral (48)", d_m, d_w)

    # n=4 extremal (10): C2xC2 latin
    r4 = ["1234", "2143", "3412", "4321"]
    m4 = [[int(c) - 1 for c in r] for r in r4]
    w4 = [[4 - int(r4[i][j]) for i in range(4)] for j in range(4)]
    describe("n=4 extremal (10)", m4, w4)


def extract_rotations(mrank, wrank):
    """Return (rotations, ple) where rotations[i] = (men_moved, women_moved)
    for the i-th join-irreducible's rotation, ple = poset order on them."""
    n = len(mrank)
    S = stable_matchings(mrank, wrank)
    k = len(S)
    le = [[all(mrank[m][S[i][m]] <= mrank[m][S[j][m]] for m in range(n))
           for j in range(k)] for i in range(k)]
    covers = [[le[i][j] and i != j and not any(
        le[i][t] and le[t][j] and t != i and t != j for t in range(k))
        for j in range(k)] for i in range(k)]
    irr = [j for j in range(k) if sum(covers[i][j] for i in range(k)) == 1]
    ple = [[le[irr[a]][irr[b]] for b in range(len(irr))] for a in range(len(irr))]
    rots = []
    for j in irr:
        i = next(i for i in range(k) if covers[i][j])
        men = tuple(sorted(m for m in range(n) if S[i][m] != S[j][m]))
        women = tuple(sorted(S[i][m] for m in men))
        rots.append((men, women))
    return rots, ple


def chain_report(name, mrank, wrank):
    n = len(mrank)
    rots, ple = extract_rotations(mrank, wrank)
    p = len(rots)
    print(f"{name}: {p} rotations, sizes {sorted(len(r[0]) for r in rots)}")
    for side, idx in (("man", 0), ("woman", 1)):
        for x in range(n):
            mine = [a for a in range(p) if x in rots[a][idx]]
            # chain iff totally ordered
            chain = all(ple[a][b] or ple[b][a] for i, a in enumerate(mine)
                        for b in mine[i + 1:])
            print(f"  {side} {x}: in {len(mine)} rotations, "
                  f"chain={'YES' if chain else 'NO'}")
