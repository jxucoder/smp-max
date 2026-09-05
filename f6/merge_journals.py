#!/usr/bin/env python3
"""Merge campaign shard journals into one journal for a single --audit.

    python3 merge_journals.py -o campaign/merged.jsonl campaign/shards/*.jsonl.gz

Inputs may be plain or gzipped JSONL.  Every input must start life as a
copy of the same snapshot (so their headers carry the same base_sha256);
the merge refuses to mix formulas.  Output: the first header, then every
non-header record in input order, with exact duplicates (same cube and
same `ts`, i.e. the snapshot prefix every shard inherited) written once.
The driver's "last record per cube wins" rule then applies to the merged
file exactly as to a single journal, so a cube that two shards both
resolved (possible only for roots processed before the partition was
introduced) keeps its later record; either is a valid certificate.

Prints per-input and merged status counts.  Exit 1 on a header mismatch
or an input without a header.
"""
import argparse
import collections
import gzip
import json
import sys


def read(path):
    op = gzip.open if path.endswith(".gz") else open
    with op(path, "rt") as f:
        for line in f:
            line = line.strip()
            if line:
                yield json.loads(line)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("inputs", nargs="+")
    ap.add_argument("-o", "--output", required=True)
    args = ap.parse_args()

    header, base = None, None
    seen, out = set(), []
    merged = {}
    for path in args.inputs:
        n, hdrs, by = 0, 0, collections.Counter()
        for r in read(path):
            if r.get("status") == "header":
                hdrs += 1
                if base is None:
                    header, base = r, r.get("base_sha256")
                elif r.get("base_sha256") != base:
                    sys.exit(f"{path}: header base_sha256 {r.get('base_sha256')} "
                             f"!= {base}; refusing to mix formulas")
                continue
            if not r.get("cube"):
                continue
            key = (r["cube"], r.get("ts"))
            if key in seen:
                continue
            seen.add(key)
            out.append(r)
            merged[r["cube"]] = r
            n += 1
            by[r["status"]] += 1
        if hdrs == 0:
            sys.exit(f"{path}: no header record")
        print(f"{path}: {n} new records {dict(by)}")
    if header is None:
        sys.exit("no header in any input")
    with open(args.output, "w") as f:
        f.write(json.dumps(header) + "\n")
        for r in out:
            f.write(json.dumps(r) + "\n")
    by = collections.Counter(r["status"] for r in merged.values())
    print(f"merged -> {args.output}: {len(out)} records, {len(merged)} cubes {dict(by)}; "
          f"next: cube_campaign.py --audit --journal {args.output}")


if __name__ == "__main__":
    main()
