"""Cube-and-conquer probe for the n=5, k=17 UNSAT proof.

Cube on man 1's full preference order (man 0 already fixed): each of the
120 orders becomes one subproblem = base CNF + 10 unit clauses on man 1's
pairwise-preference variables. Together the cubes exhaust all cases, so
UNSAT certificates for all 120 (plus a covering lemma) reprove f(5)<=16.

This probe solves a few sample cubes with kissat --plain and reports
DRAT/LRAT sizes, to calibrate whether 120 cubes suffice or we must split
deeper before the Lean import.
"""
import os
import subprocess
import sys
import time
from itertools import combinations, permutations

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from encode import build

HERE = os.path.dirname(os.path.abspath(__file__))
DT = os.path.join(HERE, "..", "dt-src", "drat-trim")


def cube_units(order):
    """Unit literals fixing man 1's preference to `order` (best first)."""
    clauses, pool, _ = build(5, 17, fix_man0=True)
    pos = {w: i for i, w in enumerate(order)}
    units = []
    for a, b in combinations(range(5), 2):
        v = pool.id(("p", "m", 1, a, b))
        units.append(v if pos[a] < pos[b] else -v)
    return clauses, pool, units


def solve_cube(idx, order):
    clauses, pool, units = cube_units(order)
    base = os.path.join(HERE, "cubes", f"cube{idx:03d}")
    cnf = base + ".cnf"
    with open(cnf, "w") as f:
        f.write(f"p cnf {pool.top} {len(clauses) + len(units)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
        for u in units:
            f.write(f"{u} 0\n")
    t0 = time.time()
    r = subprocess.run(["kissat", "-q", "--plain", cnf, base + ".drat"],
                       capture_output=True, text=True)
    dt_solve = time.time() - t0
    assert r.returncode == 20, f"cube {idx}: expected UNSAT, got rc={r.returncode}"
    t0 = time.time()
    v = subprocess.run([DT, cnf, base + ".drat", "-L", base + ".lrat"],
                       capture_output=True, text=True)
    dt_check = time.time() - t0
    assert "s VERIFIED" in v.stdout, f"cube {idx}: verification failed"
    rat = [l for l in v.stdout.splitlines() if "RAT lemmas" in l]
    sizes = {ext: os.path.getsize(base + ext) for ext in (".drat", ".lrat")}
    print(f"cube {idx:3d} order={order}: UNSAT in {dt_solve:6.1f}s, "
          f"verified in {dt_check:6.1f}s, drat={sizes['.drat']/1e6:8.2f}MB, "
          f"lrat={sizes['.lrat']/1e6:8.2f}MB, {rat[0].strip() if rat else '?'}")
    return dt_solve, sizes


if __name__ == "__main__":
    perms = list(permutations(range(5)))
    samples = [int(a) for a in sys.argv[1:]] or list(range(120))
    tot = 0.0
    for i in samples:
        s, _ = solve_cube(i, perms[i])
        tot += s
    print(f"sampled {len(samples)} cubes, mean solve {tot/len(samples):.1f}s "
          f"-> est. total for 120 cubes: {120 * tot / len(samples) / 60:.0f} min")
