# Solver and checker setup

Run these commands from the repository root. First follow the
[verification guide](../verification.md) to build Lean, expand the journal,
and check formula identity. Recorded timings describe the original runs.

## Pinned toolchain

The driver uses `cadical-src/build/cadical` and `cake_lpr-src/cake_lpr`
at the repository root. Set `SMP_TOOLCHAIN_ROOT` to use a different parent directory. Pinned versions: CaDiCaL commit
`c60730422e758ef1cebe7aeddf2dda31c996bf04` (version 3.0.1); cake_lpr from
[tanyongkiam/cake_lpr](https://github.com/tanyongkiam/cake_lpr) at
`a36874a`. The trust base contains the checker, so check the hash of the
CakeML-generated assembly you build it from:

```bash
# CaDiCaL
git clone https://github.com/arminbiere/cadical.git cadical-src
cd cadical-src && git checkout c60730422e758ef1cebe7aeddf2dda31c996bf04 && ./configure && make && cd ..
cadical-src/build/cadical --build | head -1     # Version 3.0.1 c60730422e758ef1cebe7aeddf2dda31c996bf04

# cake_lpr
git clone https://github.com/tanyongkiam/cake_lpr.git cake_lpr-src
cd cake_lpr-src && git checkout a36874a
shasum -a 256 cake_lpr.S cake_lpr_arm8.S
# 2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a  cake_lpr.S
# 95b64883edc0cb09feedbcb1ebec233e2490f5b458fdda9dc29c212ed916f00c  cake_lpr_arm8.S
gcc -O2 basis_ffi.c cake_lpr.S -o cake_lpr -std=c99        # x86-64
cc basis_ffi.c cake_lpr_arm8.S -o cake_lpr -std=c99        # arm64 (Apple silicon); use one of the two lines
./cake_lpr example.cnf example.lpr                          # s VERIFIED UNSAT
cd ..
```

The x86-64 build is what checked the container-origin records, the arm64
build what checked the Mac-origin records (per-machine counts:
`docs/results.md`). `basis_ffi.c` provides the runtime I/O interface; the recorded assembly
hashes identify the verified checker build. The compiler, runtime and
operating environment remain part of executing that checker.

## Positive control

The dihedral schedule in canonical form, pinned as a 15-unit prefix, must
be satisfiable at k = 48 and unsatisfiable at k = 49 (needs the `lake
build export_sched_cnf` from the verification guide and the CaDiCaL built above; the exports and
the solves take seconds):

```bash
mkdir -p runs/f6/positive-control
cd runs/f6/positive-control
P='0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5'
../../../lean/.lake/build/bin/export_sched_cnf pc48.cnf --k=48 "--prefix=$P"
../../../cadical-src/build/cadical -q pc48.cnf | grep '^s '      # s SATISFIABLE
../../../lean/.lake/build/bin/export_sched_cnf pc49.cnf --k=49 "--prefix=$P"
../../../cadical-src/build/cadical -q pc49.cnf | grep '^s '      # s UNSATISFIABLE
```

To see that the k = 48 model is the pinned schedule with 48 distinct
selected matchings, the Python writer (whose base formula is
byte-identical to Lean's, 3.4) can solve and decode the same cube; this
uses kissat on `PATH` (see the verification guide):

```bash
P='0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5'
python3 tools/schedule_encoding.py 6 48 runs/f6/pc48.cnf "--fix-prefix=$P" --solve
# expect: SAT in …s; schedule=…   and   decoded read-off recount: sc = 48 (need >= 48) OK
```

The same instance is recounted at 48 by `python3 tools/stable_matchings.py` (its ranking
matrix is in `docs/f6.md`), and in the kernel by `dihedral6_count`.

## Re-solving the recorded sample

To verify a journal verdict independently, re-solve the cube from the
Lean-printed formula (the sha256 must match the record's `cnf_sha256`),
refute it with an LRAT-producing solver, and check the certificate with
cake_lpr or any checker you trust. The driver does exactly this per cube
(it writes the formula with the Python writer, hashes it, solves with
`cadical --lrat --binary=false`, hashes the certificate, runs cake_lpr,
deletes the files, journals the record), and `--force --cubes` makes it
re-run listed cubes into a fresh journal. The recorded run of the 205-cube
sample is `results/f6/campaign-2026-09-08/recheck_2026-09-09.txt`; its ids are the `cube`
fields of `results/f6/campaign-2026-09-08/recheck_2026-09-09.jsonl`:

```bash
mkdir -p runs/f6/recheck
python3 - <<'PY'
import json, subprocess, sys
path = 'results/f6/campaign-2026-09-08/recheck_2026-09-09.jsonl'
ids = sorted({r['cube'] for r in map(json.loads, open(path)) if 'cube' in r})
subprocess.run([sys.executable, 'tools/campaign/cube_campaign.py',
    '--solver', 'cadical', '--force', '--workers', '6', '--time', '900',
    '--journal', 'runs/f6/recheck/campaign.jsonl',
    '--scratch', 'runs/f6/recheck/scratch', '--cubes', *ids], check=True)
PY
```

Then compare the new journal with the campaign journal record by record
(last record per cube):

```bash
python3 - <<'EOF'
import json
def last(path):
    d = {}
    for line in open(path):
        r = json.loads(line)
        if 'cube' in r and 'status' in r:
            d[r['cube']] = r
    return d
old, new = last('runs/f6/campaign.jsonl'), last('runs/f6/recheck/campaign.jsonl')
ver  = sum(new[c]['status'] == 'verified' for c in new)
cnf  = sum(new[c].get('cnf_sha256')  == old[c].get('cnf_sha256')  for c in new)
lrat = sum(new[c].get('lrat_sha256') == old[c].get('lrat_sha256') for c in new)
print(f'cubes={len(new)} verified={ver} cnf_sha256_equal={cnf} lrat_sha256_equal={lrat}')
EOF
```

Expected, as in `results/f6/campaign-2026-09-08/recheck_2026-09-09.txt`: 205 / 205 verified,
205 / 205 `cnf_sha256` equal, 204 / 205 `lrat_sha256` equal (on arm64; the
one difference is a container-origin record whose proof trace differs
across architectures). The CNF hashes must always match: they say the
formula you solved is the formula the campaign solved. The LRAT hashes
reproduce only with a bit-identical solver build; a mismatch there is a
different proof of the same formula, and the verdict is what counts. The
run took 263 s wall with 6 workers on an M4 laptop.

Any other cubes can be passed the same way (`--cubes`, ids from
`all_ids.txt` from the verification guide). Re-solving the whole tree is about 300 core-hours
of solver time plus checking; `docs/reference/campaign.md` describes the splitting
rules, so a full re-run can follow the same tree (`--cubes` over
`runs/f6/lean-identity/verified-ids.txt`) or grow its own from the roots.

Corroboration, not evidence: an earlier exhaustive enumeration of all
schedules (`experiments/enumeration/enumerate_cycle_schedules.c`; rebuild with
`cc -O2 -o gen_enum_c experiments/enumeration/enumerate_cycle_schedules.c`) also gives a maximum
of 48.
