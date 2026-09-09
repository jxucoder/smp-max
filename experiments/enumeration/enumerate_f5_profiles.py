"""Enumerate all canonical (man0=id) profiles of order 5 with >=16 (= exactly 16)
stable matchings, split by man 1's preference order. Verifies A344669(5)."""

from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

import sys, time
from itertools import combinations, permutations
from tools.direct_encoding import build
from pysat.solvers import Cadical195

idx = int(sys.argv[1])
order = list(permutations(range(5)))[idx]
clauses, pool, _ = build(5, 16, fix_man0=True)
pos = {w: i for i, w in enumerate(order)}
for a, b in combinations(range(5), 2):
    v = pool.id(("p", "m", 1, a, b))
    clauses.append([v if pos[a] < pos[b] else -v])
prefvars = [pool.id(("p", s, i, a, b)) for s in ("m", "w") for i in range(5)
            for a in range(5) for b in range(a + 1, 5)]
n = 0
t0 = time.time()
with Cadical195(bootstrap_with=clauses) as S:
    while S.solve():
        mset = set(S.get_model())
        proj = [v if v in mset else -v for v in prefvars]
        n += 1
        S.add_clause([-l for l in proj])
print(f"cube {idx:3d}: {n} solutions in {time.time()-t0:.0f}s")
