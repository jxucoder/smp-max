"""Brute-force stable-matching counter and Latin-instance sanity checks.

Conventions: participants are zero-indexed; mpref[m] and wpref[w] list
partners best first; a matching mu maps each man m to woman mu[m].
The built-in order-5 Latin check has 9 matchings, not the extremal 16.
Use tools/verify_witnesses.py for the saved extremal witnesses."""
from itertools import permutations


def ranks(pref):
    n = len(pref)
    r = [[0] * n for _ in range(n)]
    for i in range(n):
        for pos, j in enumerate(pref[i]):
            r[i][j] = pos
    return r


def stable_matchings(mpref, wpref):
    """Return the list of stable matchings of the instance."""
    n = len(mpref)
    mrank = ranks(mpref)
    wrank = ranks(wpref)
    out = []
    for mu in permutations(range(n)):
        inv = [0] * n
        for m in range(n):
            inv[mu[m]] = m
        stable = True
        for m in range(n):
            rm = mrank[m]
            thr = rm[mu[m]]
            if thr == 0:
                continue
            wr = wrank
            for w in range(n):
                if rm[w] < thr and wr[w][m] < wr[w][inv[w]]:
                    stable = False
                    break
            if not stable:
                break
        if stable:
            out.append(mu)
    return out


def count_stable(mpref, wpref):
    return len(stable_matchings(mpref, wpref))


def latin_instance(rows):
    """OEIS A351413 convention: rows[i][j] = rank (1-based) man i assigns woman j.
    Latin condition: woman j assigns man i rank n+1-rows[i][j]."""
    n = len(rows)
    mpref = []
    for i in range(n):
        order = sorted(range(n), key=lambda j: rows[i][j])
        mpref.append(tuple(order))
    wpref = []
    for j in range(n):
        order = sorted(range(n), key=lambda i: n + 1 - rows[i][j])
        wpref.append(tuple(order))
    return mpref, wpref


def parse_matrix(s):
    return [[int(c) for c in row] for row in s.split()]


if __name__ == "__main__":
    # Known extremal Latin instances from OEIS A351413.
    tests = [
        ("123 231 312", 3),
        ("1234 2143 3412 4321", 10),
        ("12345 21453 34512 45231 53124", 9),
        ("123456 214365 365214 456123 541632 632541", 48),
    ]
    failed = False
    for mat, expect in tests:
        mpref, wpref = latin_instance(parse_matrix(mat))
        got = count_stable(mpref, wpref)
        status = "OK" if got == expect else "FAIL"
        print(f"n={len(mpref)}: expected {expect}, got {got}  [{status}]")
        failed = failed or got != expect
    if failed:
        raise SystemExit(1)
