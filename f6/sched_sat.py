#!/usr/bin/env python3
"""SAT encoding of "some legal schedule of order n has sc(R(S)) >= k".

Pilot for REPLAY_DESIGN.md Architecture 3. Bounded-model-checking style:
F = n(n-1)/2 frames; per frame a one-hot step choice (cyclic move or
stop), one-hot matching state, monotone visited masks. Read-off
preference comparisons are derived from first-visit order (trajectory
prefix, bottom canonical); k selector slots assert k distinct stable
matchings of the read-off, exactly as in the f(5) selector encoding.

Budgets: per-man cap and total move budget are implied by no-revisit
(each person has only n potential partners), so only the frame bound is
structural. No symmetry breaking in v1 (measurement baseline).

Usage:
  python3 sched_sat.py N K out.cnf          # write DIMACS
  python3 sched_sat.py N K out.cnf --solve  # also run kissat, decode SAT
"""
import itertools, subprocess, sys, time


def cyclic_shapes(n):
    """All cyclic moves on 2..n men, min-first form (m_i takes current
    wife of m_{i+1})."""
    shapes = []
    for kk in range(2, n + 1):
        for men in itertools.combinations(range(n), kk):
            for rest in itertools.permutations(men[1:]):
                shapes.append((men[0],) + rest)
    return shapes


class Enc:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def new(self):
        self.n += 1
        return self.n

    def add(self, *lits):
        self.clauses.append(list(lits))

    def write(self, path):
        with open(path, "w") as f:
            f.write(f"p cnf {self.n} {len(self.clauses)}\n")
            for c in self.clauses:
                f.write(" ".join(map(str, c)) + " 0\n")


def build(n, k):
    e = Enc()
    F = n * (n - 1) // 2                      # frame bound
    SH = cyclic_shapes(n)
    NS = len(SH)

    # variables
    M = [[[e.new() for _ in range(n)] for _ in range(n)] for _ in range(F + 1)]
    V = [[[e.new() for _ in range(n)] for _ in range(n)] for _ in range(F + 1)]
    S = [[e.new() for _ in range(NS + 1)] for _ in range(F)]   # index 0 = stop

    # initial state: identity matching, visited = diagonal
    for m in range(n):
        for w in range(n):
            e.add(M[0][m][w] if m == w else -M[0][m][w])
            e.add(V[0][m][w] if m == w else -V[0][m][w])

    # one-hot rows and injective columns for every frame's matching
    for t in range(F + 1):
        for m in range(n):
            e.add(*[M[t][m][w] for w in range(n)])
            for w1 in range(n):
                for w2 in range(w1 + 1, n):
                    e.add(-M[t][m][w1], -M[t][m][w2])
        for w in range(n):
            for m1 in range(n):
                for m2 in range(m1 + 1, n):
                    e.add(-M[t][m1][w], -M[t][m2][w])

    # step choice one-hot; stop absorbs
    for t in range(F):
        e.add(*S[t])
        for a in range(NS + 1):
            for b in range(a + 1, NS + 1):
                e.add(-S[t][a], -S[t][b])
        if t + 1 < F:
            e.add(-S[t][0], S[t + 1][0])

    # transitions
    for t in range(F):
        # stop: frame copied
        for m in range(n):
            for w in range(n):
                e.add(-S[t][0], -M[t][m][w], M[t + 1][m][w])
        for j, sh in enumerate(SH, start=1):
            kk = len(sh)
            moved = set(sh)
            for i in range(kk):
                a, b = sh[i], sh[(i + 1) % kk]       # a takes b's wife
                for w in range(n):
                    e.add(-S[t][j], -M[t][b][w], M[t + 1][a][w])
            for m in range(n):
                if m in moved:
                    continue
                for w in range(n):
                    e.add(-S[t][j], -M[t][m][w], M[t + 1][m][w])
        # no-revisit: a newly acquired partner must be fresh
        for m in range(n):
            for w in range(n):
                e.add(-M[t + 1][m][w], M[t][m][w], -V[t][m][w])
        # visited update: V_{t+1} <-> V_t \/ M_{t+1}
        for m in range(n):
            for w in range(n):
                e.add(-V[t][m][w], V[t + 1][m][w])
                e.add(-M[t + 1][m][w], V[t + 1][m][w])
                e.add(-V[t + 1][m][w], V[t][m][w], M[t + 1][m][w])

    # first-visit-order auxiliaries: C[m][a][b][t] <-> V_t[m][a] /\ ~V_t[m][b]
    # before(m,a,b) = OR_t C  ("a visited strictly before b", includes
    # a-visited-b-never at t = F)
    before = {}
    for m in range(n):
        for a in range(n):
            for b in range(n):
                if a == b:
                    continue
                cs = []
                for t in range(F + 1):
                    c = e.new()
                    e.add(-c, V[t][m][a])
                    e.add(-c, -V[t][m][b])
                    e.add(c, -V[t][m][a], V[t][m][b])
                    cs.append(c)
                bv = e.new()
                for c in cs:
                    e.add(-c, bv)
                e.add(-bv, *cs)
                before[(m, a, b)] = bv

    # neither[m][{a,b}] <-> ~V_F[m][a] /\ ~V_F[m][b]
    neither = {}
    for m in range(n):
        for a in range(n):
            for b in range(a + 1, n):
                nv = e.new()
                e.add(-nv, -V[F][m][a])
                e.add(-nv, -V[F][m][b])
                e.add(nv, V[F][m][a], V[F][m][b])
                neither[(m, a, b)] = nv

    # men's read-off preference: PM[m][a][b] ("m prefers woman a to b")
    #   <-> before(m,a,b) \/ (neither /\ a<b)
    PM = {}
    for m in range(n):
        for a in range(n):
            for b in range(n):
                if a == b:
                    continue
                p = e.new()
                bv = before[(m, a, b)]
                if a < b:
                    nv = neither[(m, a, b)]
                    e.add(-bv, p)
                    e.add(-nv, p)
                    e.add(-p, bv, nv)
                else:
                    e.add(-bv, p)
                    e.add(-p, bv)
                PM[(m, a, b)] = p

    # women's read-off preference: PW[w][a][b] ("w prefers man a to b")
    # reversed trajectory: later-first among visited; visited over never;
    # canonical among never. VW_t[w][m] := V[t][m][w].
    # both visited, a later  <-> before_w(b,a) /\ V_F[a]
    # a visited, b never     <-> V_F[a] /\ ~V_F[b]
    # neither                -> a<b
    beforeW = {}
    for w in range(n):
        for a in range(n):
            for b in range(n):
                if a == b:
                    continue
                cs = []
                for t in range(F + 1):
                    c = e.new()
                    e.add(-c, V[t][a][w])
                    e.add(-c, -V[t][b][w])
                    e.add(c, -V[t][a][w], V[t][b][w])
                    cs.append(c)
                bv = e.new()
                for c in cs:
                    e.add(-c, bv)
                e.add(-bv, *cs)
                beforeW[(w, a, b)] = bv
    PW = {}
    for w in range(n):
        for a in range(n):
            for b in range(n):
                if a == b:
                    continue
                p = e.new()
                later = e.new()                     # b before a, a visited
                e.add(-later, beforeW[(w, b, a)])
                e.add(-later, V[F][a][w])
                e.add(later, -beforeW[(w, b, a)], -V[F][a][w])
                only_a = e.new()                    # a visited, b never
                e.add(-only_a, V[F][a][w])
                e.add(-only_a, -V[F][b][w])
                e.add(only_a, -V[F][a][w], V[F][b][w])
                terms = [later, only_a]
                if a < b:
                    nv = e.new()
                    e.add(-nv, -V[F][a][w])
                    e.add(-nv, -V[F][b][w])
                    e.add(nv, V[F][a][w], V[F][b][w])
                    terms.append(nv)
                for tv in terms:
                    e.add(-tv, p)
                e.add(-p, *terms)
                PW[(w, a, b)] = p

    # selector block: k slots over the n! matchings
    P = list(itertools.permutations(range(n)))
    Y = [[e.new() for _ in P] for _ in range(k)]
    for t in range(k):
        e.add(*Y[t])
    for t in range(k - 1):
        for i in range(len(P)):
            for j in range(i + 1):
                e.add(-Y[t][i], -Y[t + 1][j])
    for t in range(k):
        for i, mu in enumerate(P):
            inv = [0] * n
            for m in range(n):
                inv[mu[m]] = m
            for m in range(n):
                for w in range(n):
                    if w == mu[m]:
                        continue
                    e.add(-Y[t][i], -PM[(m, w, mu[m])], -PW[(w, m, inv[w])])
    return e, (M, V, S, Y, SH, F, P)


def decode(model, n, hooks):
    M, V, S, Y, SH, F, P = hooks
    pos = set(l for l in model if l > 0)
    sched = []
    for t in range(F):
        for j in range(len(SH) + 1):
            if S[t][j] in pos:
                if j > 0:
                    sched.append(SH[j - 1])
                break
    sel = []
    for t in range(len(Y)):
        for i, mu in enumerate(P):
            if Y[t][i] in pos:
                sel.append(mu)
    return sched, sel


def readoff_counts(n, sched):
    """Independent recount: apply schedule, build read-off, count stable."""
    sys.path.insert(0, ".")
    from rotation_poset import stable_matchings
    match = list(range(n))
    trajm = [[m] for m in range(n)]
    trajw = [[w] for w in range(n)]
    for sh in sched:
        old = list(match)
        for i, m in enumerate(sh):
            w = old[sh[(i + 1) % len(sh)]]
            match[m] = w
            trajm[m].append(w)
            trajw[w].append(m)
    mrank, wrank = [], []
    for m in range(n):
        order = trajm[m] + [w for w in range(n) if w not in trajm[m]]
        r = [0] * n
        for pos_, w in enumerate(order):
            r[w] = pos_
        mrank.append(r)
    for w in range(n):
        order = list(reversed(trajw[w])) + [m for m in range(n) if m not in trajw[w]]
        r = [0] * n
        for pos_, m in enumerate(order):
            r[m] = pos_
        wrank.append(r)
    return len(stable_matchings(mrank, wrank))


if __name__ == "__main__":
    n, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    e, hooks = build(n, k)
    e.write(out)
    print(f"n={n} k={k}: {e.n} vars, {len(e.clauses)} clauses -> {out}")
    if "--solve" in sys.argv:
        t0 = time.time()
        r = subprocess.run(["kissat", "-q", out], capture_output=True, text=True)
        dt = time.time() - t0
        if "s SATISFIABLE" in r.stdout:
            model = []
            for line in r.stdout.splitlines():
                if line.startswith("v "):
                    model += [int(x) for x in line[2:].split() if x != "0"]
            sched, sel = decode(model, n, hooks)
            cnt = readoff_counts(n, sched)
            print(f"SAT in {dt:.1f}s; schedule={sched}")
            print(f"decoded read-off recount: sc = {cnt} (need >= {k}) "
                  f"{'OK' if cnt >= k else 'MISMATCH!'}")
        elif "s UNSATISFIABLE" in r.stdout:
            print(f"UNSAT in {dt:.1f}s")
        else:
            print(f"solver exit {r.returncode} in {dt:.1f}s")
