#!/usr/bin/env python3
"""Merge campaign shard journals into one journal for a single --audit.

    python3 merge_journals.py -o campaign/merged.jsonl \\
        campaign/campaign.jsonl campaign/shards/*.jsonl.gz

Inputs may be plain or gzipped JSONL, in any order.  Every input must
start life as a copy of the same snapshot (so their headers carry the
same base_sha256); the merge refuses to mix formulas.

Conflict resolution is explicit, NOT by input order.  Two journals can
hold different records for the same cube (a root the pre-shard container
split by a wall-clock timeout and its owner shard later verified; a child
one driver journaled as error and another certified).  For each cube the
merged file keeps exactly one record, the best by

    SAT  >  verified  >  split  >  non-terminal (error, timeouts, ...)

and, within a class, the latest `ts`.  A `verified` record is a complete
certificate for that cube's formula and is checked by the audit on its own
(verify_record); a `split` only promises its children, so it must never
shadow a certificate.  A SAT record is a possible counterexample and is
never shadowed by anything; the merge prints it loudly.  Shard journals
keep their full history; the merged file is the audit's input.

Malformed lines (a checkpoint taken mid-append can end in a torn line)
are skipped and counted, as load_journal does.  Output: the first header,
then one record per cube in order of first appearance.  Exit 1 on a
header mismatch, an input without a header, or no usable input.
"""
import argparse
import collections
import gzip
import json
import sys

RANK = {"SAT": 3, "verified": 2, "split": 1}      # everything else: 0


def read(path):
    """(record | None, raw_line) per line; None for a line that is not JSON."""
    op = gzip.open if path.endswith(".gz") else open
    with op(path, "rt") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                yield json.loads(line)
            except json.JSONDecodeError:
                yield None


def better(a, b):
    """True if record a should replace record b for the same cube."""
    ra, rb = RANK.get(a.get("status"), 0), RANK.get(b.get("status"), 0)
    if ra != rb:
        return ra > rb
    return (a.get("ts") or 0) > (b.get("ts") or 0)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("inputs", nargs="+")
    ap.add_argument("-o", "--output", required=True)
    args = ap.parse_args()

    header, base = None, None
    chosen, order = {}, []          # cube -> best record; cubes in first-appearance order
    dropped = collections.Counter()  # status of records shadowed by a better one
    for path in args.inputs:
        n, hdrs, torn, by = 0, 0, 0, collections.Counter()
        for r in read(path):
            if r is None:
                torn += 1
                continue
            if r.get("status") == "header":
                hdrs += 1
                if base is None:
                    header, base = r, r.get("base_sha256")
                elif r.get("base_sha256") != base:
                    sys.exit(f"{path}: header base_sha256 {r.get('base_sha256')} "
                             f"!= {base}; refusing to mix formulas")
                continue
            cid = r.get("cube")
            if not cid:
                continue
            n += 1
            by[r.get("status")] += 1
            cur = chosen.get(cid)
            if cur is None:
                chosen[cid] = r
                order.append(cid)
            elif better(r, cur):
                dropped[cur.get("status")] += 1
                chosen[cid] = r
            else:
                dropped[r.get("status")] += 1
        if hdrs == 0:
            sys.exit(f"{path}: no header record")
        print(f"{path}: {n} records {dict(by)}"
              + (f"; {torn} malformed line(s) skipped" if torn else ""))
    if header is None:
        sys.exit("no header in any input")
    with open(args.output, "w") as f:
        f.write(json.dumps(header) + "\n")
        for cid in order:
            f.write(json.dumps(chosen[cid]) + "\n")
    by = collections.Counter(r.get("status") for r in chosen.values())
    print(f"merged -> {args.output}: {len(order)} cubes {dict(by)}; "
          f"shadowed records dropped: {dict(dropped) or 0}; "
          f"next: cube_campaign.py --audit --journal {args.output}")
    for cid, r in chosen.items():
        if r.get("status") == "SAT":
            print(f"!!! SAT record kept for cube {cid}: verdict={r.get('verdict')}")


if __name__ == "__main__":
    main()
