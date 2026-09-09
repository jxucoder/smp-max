#!/usr/bin/env python3
"""Recompute every journaled cnf_sha256 from Lean-printed pieces.

    python3 lean_rehash.py BASE.cnf UNITS.tsv JOURNAL.jsonl

BASE.cnf   : `export_sched_cnf BASE.cnf` (the base formula; header
             `p cnf 84882 2709212`, sha256 28421fb6...)
UNITS.tsv  : `export_cubes6 UNITS.tsv --units=ids.txt` (id<TAB>unit lines
             joined by '|', from `prefixUnits`/`stopUnits`)
JOURNAL    : the campaign journal (JSONL); every record carrying a
             `cnf_sha256` (verified and split cubes) is checked.

A cube's file is `header ‖ body ‖ units` with `header = p cnf 84882
(2709212 + #units)`; the body is shared, so its hash state is computed
once per unit count and copied.  Exit 0 iff every record matches.
"""
import hashlib, json, sys

base_path, units_path, journal_path = sys.argv[1:4]
base = open(base_path, "rb").read()
nl = base.index(b"\n")
header, body = base[:nl], base[nl + 1:]
assert header == b"p cnf 84882 2709212", header
states = {}


def state(n):
    if n not in states:
        h = hashlib.sha256()
        h.update(f"p cnf 84882 {2709212 + n}\n".encode())
        h.update(body)
        states[n] = h
    return states[n]


units = {}
with open(units_path) as f:
    for line in f:
        cid, _, u = line.rstrip("\n").partition("\t")
        units[cid] = [x for x in u.split("|") if x]

recs = {}
with open(journal_path) as f:
    for line in f:
        r = json.loads(line)
        if r.get("status") == "header":
            continue
        recs[r["cube"]] = r            # last record per cube wins (as --audit)

checked = matched = 0
missing, bad = [], []
for cid, r in recs.items():
    sha = r.get("cnf_sha256")
    if not sha:
        continue
    if cid not in units:
        missing.append(cid)
        continue
    u = units[cid]
    h = state(len(u)).copy()
    h.update(("".join(x + "\n" for x in u)).encode())
    checked += 1
    if h.hexdigest() == sha:
        matched += 1
    else:
        bad.append((cid, h.hexdigest()[:12], sha[:12]))
print(f"lean_rehash: records with cnf_sha256={checked} matched={matched} "
      f"mismatched={len(bad)} missing_units={len(missing)}")
for x in bad[:10]:
    print("   mismatch", *x)
for x in missing[:10]:
    print("   missing", x)
sys.exit(0 if matched == checked and not missing and checked > 0 else 1)
