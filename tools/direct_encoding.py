"""SAT encoding of: does there exist an n x n stable-marriage instance
with at least k stable matchings?

Encoding:
  - For each person (side, i) and unordered pair a<b of the opposite side,
    a boolean P[side][i][(a,b)] meaning "i prefers a over b".
  - Transitivity: forbid both 3-cycles per unordered triple (2 clauses each).
  - For each perfect matching mu (as tuple mu[m]=w), an indicator S_mu with
    S_mu -> stability: for every non-matched pair (m,w),
      not(m prefers w over mu(m)  AND  w prefers m over mu(w)).
    Only this direction is needed: for ">= k" the solver must raise k
    indicators, and any raised indicator certifies a genuinely stable mu,
    so SAT answers give valid instances and UNSAT refutes ">= k".
  - Cardinality: sum(S_mu) >= k  (pysat sequential counter).
  - Optional symmetry breaking (for UNSAT runs): fix man 0's preference
    list to the identity order (kills the n! woman-relabeling symmetry).

Solution decoding returns (mpref, wpref) for independent recount.
"""

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from itertools import combinations, permutations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195


def build(n, k, fix_man0=False):
    pool = IDPool()

    def pvar(side, i, a, b):
        """True iff person i on `side` prefers a over b (any a != b)."""
        if a < b:
            return pool.id(("p", side, i, a, b))
        return -pool.id(("p", side, i, b, a))

    clauses = []
    # Transitivity per person: forbid p(a,b) & p(b,c) & p(c,a) for both cycle
    # orientations of each unordered triple.
    for side in ("m", "w"):
        for i in range(n):
            for a, b, c in combinations(range(n), 3):
                clauses.append([-pvar(side, i, a, b), -pvar(side, i, b, c), -pvar(side, i, c, a)])
                clauses.append([-pvar(side, i, b, a), -pvar(side, i, c, b), -pvar(side, i, a, c)])

    # Stability indicators.
    svars = []
    for mu in permutations(range(n)):
        s = pool.id(("s", mu))
        svars.append(s)
        for m in range(n):
            for w in range(n):
                if mu[m] == w:
                    continue
                m2 = mu.index(w)  # w's partner
                w2 = mu[m]        # m's partner
                # not(S & m prefers w over w2 & w prefers m over m2)
                clauses.append([-s, -pvar("m", m, w, w2), -pvar("w", w, m, m2)])

    if fix_man0:
        for a, b in combinations(range(n), 2):
            clauses.append([pvar("m", 0, a, b)])

    card = CardEnc.atleast(lits=svars, bound=k, vpool=pool, encoding=EncType.seqcounter)
    return clauses + card.clauses, pool, svars


def decode(model, pool, n):
    pos = set(v for v in model if v > 0)

    def prefers(side, i, a, b):
        if a < b:
            return pool.id(("p", side, i, a, b)) in pos
        return pool.id(("p", side, i, b, a)) not in pos

    mpref, wpref = [], []
    for side, out in (("m", mpref), ("w", wpref)):
        for i in range(n):
            order = sorted(range(n), key=lambda x: sum(not prefers(side, i, x, y) for y in range(n) if y != x))
            out.append(tuple(order))
    return mpref, wpref


def solve(n, k, fix_man0=False, verbose=True):
    clauses, pool, _ = build(n, k, fix_man0=fix_man0)
    if verbose:
        nv = pool.top
        print(f"n={n} k>={k}: {nv} vars, {len(clauses)} clauses")
    with Cadical195(bootstrap_with=clauses) as solver:
        sat = solver.solve()
        if not sat:
            return None
        return decode(solver.get_model(), pool, n)


def export_dimacs(n, k, path, fix_man0=False):
    clauses, pool, _ = build(n, k, fix_man0=fix_man0)
    with open(path, "w") as f:
        f.write(f"p cnf {pool.top} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    print(f"wrote {path}: {pool.top} vars, {len(clauses)} clauses")


if __name__ == "__main__":
    import sys
    import time

    from tools.stable_matchings import count_stable

    n = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 16
    fix = "--fix-man0" in sys.argv
    if "--dimacs" in sys.argv:
        out = sys.argv[sys.argv.index("--dimacs") + 1]
        export_dimacs(n, k, out, fix_man0=fix)
        sys.exit(0)
    t0 = time.time()
    res = solve(n, k, fix_man0=fix)
    dt = time.time() - t0
    if res is None:
        print(f"UNSAT: no {n}x{n} instance with >= {k} stable matchings ({dt:.1f}s)")
    else:
        mpref, wpref = res
        c = count_stable(mpref, wpref)
        print(f"SAT in {dt:.1f}s; independent recount: {c} stable matchings")
        print("mpref:", mpref)
        print("wpref:", wpref)
        assert c >= k, "encoding bug: recount below bound!"
