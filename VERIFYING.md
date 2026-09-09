# Verifying f(5) = 16 and f(6) = 48 from scratch

This guide lets a third party check every link of the evidence chain on
their own machine, **without trusting any run we performed**. It is one
linear recipe: the fast path (section 2) takes about 30 minutes and
re-establishes everything that is a theorem or a file identity; the full
sections re-solve the certificates, which is what "without trusting any
run we performed" means for the certificate layer (about 2–3 hours for
f(5), about 300 core-hours for the whole f(6) tree, minutes for a sample).

Contents

0. What you end up trusting (and nothing else)
1. Prerequisites
2. Fast path (about 30 minutes)
3. f(6) = 48 in full
4. f(5) = 16 in full
5. What is and is not a theorem
6. Known gaps
7. Appendix: the 25 theorems CI checks

Campaign numbers (cube counts, split counts, solver time, provenance per
machine) live in one place, `STATUS.md`; this file quotes them only where
they are the expected output of a command.

## 0. What you end up trusting (and nothing else)

One list, valid for both results:

1. **Lean 4's kernel** (small, independently re-implementable; you can
   additionally replay every module through the kernel with Lean's
   `leanchecker`, section 3.8).
2. **Three standard axioms**: `propext`, `Classical.choice`, `Quot.sound`
   (`lean/Witness.lean` needs only `propext`).
3. **About 40 lines of definitions**, the one irreducibly human step: YOU
   must read them and agree they say "n × n stable-marriage instance" and
   "number of stable matchings". For f(5): `Inst`, `WF`, `isStable`,
   `stableCount` in `lean/SmpF5/SmpF5/Faithful.lean`. For f(6): `Inst6`,
   `WF6`, `isStable6`, `sms6`, `stableCount6` at the top of
   `lean/SmpF5/SmpF5/SixBridge.lean`.
4. **One LRAT proof checker of your choice.** We used cake_lpr, whose
   correctness is itself machine-checked down to machine code; you may
   substitute any checker (drat-trim, lrat-check, verified Coq/Lean
   checkers). Checker diversity replaces trust.
5. **The printers**, together with the file identity between what Lean
   prints and what the checker checked: for f(5) the 20-line DIMACS
   printer `lean/SmpF5/ExportCnf.lean` (you regenerate the 120 formulas
   yourself, so no identity check is needed); for f(6)
   `lean/SmpF5/ExportSchedCnf.lean` (the formula and any single cube) and
   `lean/SmpF5/ExportCubes6.lean` (the cube ids and unit clauses), plus the
   identity checks of section 3.4, which show that every formula the
   campaign solved is byte for byte what these printers print from the
   Lean definitions.
6. **For f(6) only: the campaign journal**
   (`f6/campaign/campaign.jsonl.gz`), and it is self-attested. A
   `verified` record is the driver's transcription of cake_lpr's verdict
   (`s VERIFIED UNSAT`, exit 0) for that cube; the certificates (about
   25 TB) were deleted after checking; the audit (section 3.4) checks the
   records' consistency, not the certificates. Independently verifying a
   verdict means re-solving that cube from the Lean-printed formula
   (section 3.7); the per-cube `cnf_sha256` and `lrat_sha256` make a
   re-run comparable with the journal record by record. Re-solving the
   whole tree is about 300 core-hours of solver time; a 205-cube sample
   has been re-solved on a second machine
   (`f6/campaign/recheck_2026-09-09.txt`). For f(5) there is no journal
   to trust: you regenerate and re-check all 120 formulas.

Not on the list: our solver runs, our Python scripts, our honesty.

## 1. Prerequisites

- **OS**: macOS or Linux, arm64 or x86-64 (the campaign ran on both; CI
  runs on `ubuntu-latest`).
- **The repository**: `git clone --depth 1 https://github.com/jxucoder/smp-max`
  — the history holds superseded journal snapshots and is large; the tip
  is all you need.
- **Lean**: [elan](https://github.com/leanprover/elan); the file
  `lean/SmpF5/lean-toolchain` pins Lean `v4.33.1`, which elan installs on
  the first `lake` command. `lake exe cache get` downloads the prebuilt
  Mathlib (or build it from source if paranoid).
- **Disk**: about 8 GB for `lean/SmpF5/.lake` (Mathlib plus this
  development). Re-solving needs scratch space for certificates: f(5)
  cubes are about 0.5 GB each transiently; f(6) certificates are median
  35 MB and up to 9.8 GB each (`STATUS.md`), deleted by the driver after
  checking.
- **Python 3**, standard library only (`f6/cube_campaign.py`,
  `f6/lean_rehash.py`, `f6/sched_sat.py`, `smp.py`).
- **Solvers and checker**, only for re-solving (sections 3.5 to 3.7 and
  4): CaDiCaL and cake_lpr for f(6) (built in section 3.5 into the
  gitignored directories `cadical-src/` and `cake_lpr-src/` at the clone
  root, where the driver expects them); kissat 4.0.4 and drat-trim
  additionally for the f(5) loop (section 4).

Convention: every command block below starts at the clone root
(`smp-max/`). Blocks that need another directory begin with an explicit
`cd` line; start the next block from the root again.

## 2. Fast path (about 30 minutes)

| # | command (from the clone root) | expected output | minutes |
|---|---|---|---|
| 1 | `cd lean/SmpF5 && lake exe cache get && lake build` | build ends without errors (893 jobs) | ~20 |
| 2 | `cd lean/SmpF5 && grep -rn sorry SmpF5/` | no output (exit 1) | <1 |
| 3 | `#print axioms f6_eq_48_of_unsat` and `f5_eq_16_of_unsat` (block below) | both `[propext, Classical.choice, Quot.sound]` | 1 |
| 4 | `gunzip -k f6/campaign/campaign.jsonl.gz && python3 f6/cube_campaign.py --audit --journal f6/campaign/campaign.jsonl` | `audit: roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0`, `audit: OK`, exit 0 | <1 |
| 5 | `export_cubes6 final.txt --final`, sorted, vs the journal's verified ids (block below) | `cmp` silent; `wc -l` 318736 | 1 |
| 6 | `export_cubes6 units.tsv --units=all_ids.txt` then `f6/lean_rehash.py` (block below) | `lean_rehash: records with cnf_sha256=321492 matched=321492 mismatched=0 missing_units=0`, exit 0 | ~3 |

As one runnable sequence:

```bash
# 1–2: build and no-sorry check
cd lean/SmpF5
lake exe cache get
lake build
grep -rn sorry SmpF5/            # must print nothing

# 3: axiom bases of the two main theorems
printf 'import SmpF5.Lower\n#print axioms f5_eq_16_of_unsat\n' > ax5.lean
printf 'import SmpF5.Bridge6\n#print axioms f6_eq_48_of_unsat\n' > ax6main.lean
lake env lean ax5.lean           # 'f5_eq_16_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean ax6main.lean       # 'f6_eq_48_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
cd ../..

# 4: journal audit
gunzip -k f6/campaign/campaign.jsonl.gz
python3 f6/cube_campaign.py --audit --journal f6/campaign/campaign.jsonl
# expect: audit: roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0
#         audit: OK   and exit status 0

# 5–6: certified cube set and every cube formula's hash, from the Lean definitions
cd lean/SmpF5
lake build export_sched_cnf export_cubes6
python3 - <<'EOF'
import json
last = {}
for line in open('../../f6/campaign/campaign.jsonl'):
    r = json.loads(line)
    if 'cube' in r and 'status' in r:
        last[r['cube']] = r                      # last record per cube wins
w = lambda name, ids: open(name, 'w').write(''.join(i + '\n' for i in ids))
w('all_ids.txt', last)
w('verified.txt', [c for c, r in last.items() if r['status'] == 'verified'])
w('split_ids.txt', [c for c, r in last.items() if r['status'] == 'split'])
EOF
.lake/build/bin/export_cubes6 final.txt --final
sort final.txt > a; sort verified.txt > b; cmp a b && wc -l a    # silent cmp, 318736 a
.lake/build/bin/export_sched_cnf base.cnf
.lake/build/bin/export_cubes6 units.tsv --units=all_ids.txt
python3 ../../f6/lean_rehash.py base.cnf units.tsv ../../f6/campaign/campaign.jsonl
# expect: lean_rehash: records with cnf_sha256=321492 matched=321492 mismatched=0 missing_units=0
#         and exit status 0
# scratch outputs of this block (ax*.lean, *_ids.txt, verified.txt, final.txt, a, b, base.cnf, units.tsv)
# live in lean/SmpF5 and can be deleted afterwards; f6/campaign/campaign.jsonl is gitignored
```

What this buys you: both theorems are kernel-checked over the definitions
of item 3 with the standard axioms and no holes; the f(6) journal is
internally consistent; the Lean-defined certified cube set is exactly the
set of cubes the journal records as verified; and every formula hash the
driver recorded before solving recomputes from Lean-printed pieces. What
remains is the journal's self-attestation (item 6), addressed by
re-solving (section 3.7), and the f(5) certificates, regenerated in
section 4.

## 3. f(6) = 48 in full

### 3.1 The theorem

`f6_eq_48_of_unsat` in `lean/SmpF5/SmpF5/Bridge6.lean`:

```
(∀ c ∈ Cubes6.finalCubes, ¬Satisfiable (Cubes6.cubeFormula 49 c)) →
  (∀ (I : Inst6), WF6 I = true → stableCount6 I ≤ 48) ∧ ∃ I, WF6 I = true ∧ stableCount6 I = 48
```

Read as: IF every cube formula of the certified cube set is unsatisfiable
THEN f(6) = 48, the upper bound for every well-formed order-6 instance
together with a witness with exactly 48 (`dihedral6_count`, kernel-computed
in `Lower6.lean`). `Cubes6.finalCubes` and `Cubes6.cubeFormula` are Lean
definitions; section 3.4 shows they are exactly the cubes and formulas the
campaign refuted. To print the statement and its axioms yourself:

```bash
cd lean/SmpF5
printf 'import SmpF5.Bridge6\n#print axioms f6_eq_48_of_unsat\n#check @f6_eq_48_of_unsat\n' > ax6main.lean
lake env lean ax6main.lean
# expect: 'f6_eq_48_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
#         followed by the statement above
```

### 3.2 The chain in five sentences

Every well-formed order-6 instance is dominated by the read-off instance
of some legal transposition schedule (`validity_unconditional`, the
reduction layer). Any such schedule can be relabeled to first-appearance
canonical form without lowering the count (`exists_canonical_schedule`).
Every legal canonical schedule fits one of the cubes of `finalCubes`
(`fits_final`). If the read-off has at least 49 stable matchings, the
schedule's natural assignment satisfies that cube's formula
(`cube_faithful6`), so an unsatisfiable cube set leaves no instance with
49 (`f6_upper_of_unsat`). The dihedral instance has exactly 48 by kernel
computation (`dihedral6_count`), and `f6_eq_48_of_unsat` conjoins the two.

### 3.3 The 25 theorems CI checks (~5 min)

CI (`.github/workflows/lean-verify.yml`) checks the axiom base of 25
named theorems of the order-6 development in addition to
`f5_eq_16_of_unsat`. To repeat:

```bash
cd lean/SmpF5
echo 'import SmpF5
#print axioms bridge
#print axioms chain_complete
#print axioms traj_mem_iff
#print axioms wtraj_nodup
#print axioms total_moves_le_30
#print axioms count_le_of_orderPreserving
#print axioms sc_le_readoffS_chainSched
#print axioms manOpt_wrelabel6
#print axioms validity_unconditional
#print axioms PM_sem
#print axioms PW_sem
#print axioms Legal_length_le_15
#print axioms minFirst_mem_cyclicShapes
#print axioms permsN6_perm_permutations
#print axioms Legal_map_minFirst
#print axioms SchedCNF6.dec_pwVar3
#print axioms firstApp_relabel
#print axioms Legal_relabel
#print axioms sc_le_readoffS_relabelSched
#print axioms exists_canonical_schedule
#print axioms fits_final
#print axioms cube_faithful6
#print axioms dihedral6_count
#print axioms f6_upper_of_unsat
#print axioms f6_eq_48_of_unsat' > ax6.lean && lake env lean ax6.lean
```

All 25 must report `[propext, Classical.choice, Quot.sound]`. What each
theorem says, and which file it lives in, is the appendix (section 7).

### 3.4 The certificate campaign: audit and Lean identity checks (~10 min)

The hypothesis of the theorem is discharged by the certificate campaign:
the Lean-defined formula `SchedCNF6.schedCNF49` was refuted over a tree of
cubes whose leaves are `finalCubes`, each leaf by CaDiCaL with the
certificate accepted by cake_lpr (numbers: `STATUS.md`; provenance:
`f6/CAMPAIGN.md`). The journal `f6/campaign/campaign.jsonl.gz` has one
record per attempt; the last record per cube wins. Reference hash:

```
shasum -a 256 f6/campaign/campaign.jsonl.gz
c9026b08045d8e8824c66d213bfa8eeb5336f118c22e030d42040136be7a8e4e
```

The commands are those of fast-path steps 4 to 6, plus the root-cube and
split-children exports. All of them run from `lean/SmpF5`; the Python
snippet reads the decompressed journal by its repository path and writes
the three id files into the current directory. (Recorded run:
`f6/campaign/lean_identity.txt`.)

```bash
gunzip -k f6/campaign/campaign.jsonl.gz          # skip if already done
cd lean/SmpF5
lake build export_sched_cnf export_cubes6
python3 - <<'EOF'
import json
last = {}
for line in open('../../f6/campaign/campaign.jsonl'):
    r = json.loads(line)
    if 'cube' in r and 'status' in r:
        last[r['cube']] = r                      # last record per cube wins
w = lambda name, ids: open(name, 'w').write(''.join(i + '\n' for i in ids))
w('all_ids.txt', last)                                                        # 321,492 ids
w('verified.txt', [c for c, r in last.items() if r['status'] == 'verified'])  # 318,736
w('split_ids.txt', [c for c, r in last.items() if r['status'] == 'split'])    # 2,756
EOF
python3 ../../f6/cube_campaign.py --audit --journal ../../f6/campaign/campaign.jsonl
# expect: audit: roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0
#         audit: OK   and exit status 0
.lake/build/bin/export_sched_cnf base.cnf          # the base formula
shasum -a 256 base.cnf                             # 28421fb68b0f494b99d1918aa64cff248443161dc7a6c220e0c3e895a67df59b
.lake/build/bin/export_cubes6 roots.txt            # Cubes6.canonicalCubes2: 25,493 ids
.lake/build/bin/export_cubes6 children.tsv --parents=split_ids.txt   # extendCanon: 295,999 parent/child lines
.lake/build/bin/export_cubes6 final.txt --final    # Cubes6.finalCubes: the certified cube set
sort final.txt > a; sort verified.txt > b; cmp a b && wc -l a         # identical, 318736 lines
.lake/build/bin/export_cubes6 units.tsv --units=all_ids.txt          # each cube's unit clauses (~150 s)
python3 ../../f6/lean_rehash.py base.cnf units.tsv ../../f6/campaign/campaign.jsonl
# expect: lean_rehash: records with cnf_sha256=321492 matched=321492 mismatched=0 missing_units=0
#         and exit status 0
```

What each line shows. The **audit** checks that every root cube is
`verified` or `split` with all children recursively covered, that the
journal header's base formula hash equals the recomputed formula, and that
every `verified` record has solver rc 20, `cake_verified` with `cake_rc 0`,
no kill flag and well-formed hashes; it is a consistency check of the
journal, not a re-check of any certificate. `base.cnf` is byte-identical
to the campaign's base formula (the journal header's `base_sha256`).
`roots.txt` equals the driver's root list. `children.tsv` equals the
driver's children of every cube that was split. `final.txt`, the
Lean-defined `finalCubes` (`SplitList6.lean`: `refineCubes` of
`canonicalCubes2` by the recorded split ids), equals the set of verified
ids. And every journaled `cnf_sha256` (hashed by the driver before
solving) recomputes from the Lean-printed header, body and unit clauses.

Any single cube can also be printed in full: an open cube with id
`0,1;2,3` is `export_sched_cnf OUT --prefix='0,1;2,3'`; a closed cube
whose id ends in `;stop`, say `0,4,2,3,5,1;stop`, is
`export_sched_cnf OUT --prefix='0,4,2,3,5,1' --stop`; the root cube `stop`
is `export_sched_cnf OUT --stop` alone. Quote the argument, the ids
contain semicolons. The file's sha256 must equal that cube's journaled
`cnf_sha256`.

### 3.5 Toolchain for re-solving

The driver `f6/cube_campaign.py` expects `../cadical-src/build/cadical`
and `../cake_lpr-src/cake_lpr` relative to `f6/`, that is, the two
gitignored directories at the clone root. Pinned versions: CaDiCaL commit
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
`STATUS.md`). `basis_ffi.c` is the FFI shim, outside the trust base; the
verified checker is the assembly whose hash you just compared.

### 3.6 Positive control (encoding not vacuous)

The dihedral schedule in canonical form, pinned as a 15-unit prefix, must
be satisfiable at k = 48 and unsatisfiable at k = 49 (needs the `lake
build export_sched_cnf` of 3.4 and the CaDiCaL of 3.5; the exports and
the solves take seconds):

```bash
cd lean/SmpF5
P='0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5'
.lake/build/bin/export_sched_cnf pc48.cnf --k=48 "--prefix=$P"
../../cadical-src/build/cadical -q pc48.cnf | grep '^s '      # s SATISFIABLE
.lake/build/bin/export_sched_cnf pc49.cnf --k=49 "--prefix=$P"
../../cadical-src/build/cadical -q pc49.cnf | grep '^s '      # s UNSATISFIABLE
```

To see that the k = 48 model is the pinned schedule with 48 distinct
selected matchings, the Python writer (whose base formula is
byte-identical to Lean's, 3.4) can solve and decode the same cube; this
uses kissat on `PATH` (section 4):

```bash
P='0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5;1,2;0,5;3,4;0,1;2,3;4,5'
python3 f6/sched_sat.py 6 48 pc48.cnf "--fix-prefix=$P" --solve
# expect: SAT in …s; schedule=…   and   decoded read-off recount: sc = 48 (need >= 48) OK
```

The same instance is recounted at 48 by `python3 smp.py` (its ranking
matrix is in `f6/README.md`), and in the kernel by `dihedral6_count`.

### 3.7 Re-solving cubes: the sample and the whole tree

To verify a journal verdict independently, re-solve the cube from the
Lean-printed formula (the sha256 must match the record's `cnf_sha256`),
refute it with an LRAT-producing solver, and check the certificate with
cake_lpr or any checker you trust. The driver does exactly this per cube
(it writes the formula with the Python writer, hashes it, solves with
`cadical --lrat --binary=false`, hashes the certificate, runs cake_lpr,
deletes the files, journals the record), and `--force --cubes` makes it
re-run listed cubes into a fresh journal. The recorded run of the 205-cube
sample is `f6/campaign/recheck_2026-09-09.txt`; its ids are the `cube`
fields of `f6/campaign/recheck_2026-09-09.jsonl`:

```bash
IDS=$(python3 -c "import json; print(' '.join(sorted({r['cube'] for r in map(json.loads, open('f6/campaign/recheck_2026-09-09.jsonl')) if 'cube' in r})))")
python3 f6/cube_campaign.py --solver cadical --force --workers 6 --time 900 \
    --journal f6/campaign/recheck_new.jsonl --scratch f6/campaign/scratch_recheck --cubes $IDS
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
old, new = last('f6/campaign/campaign.jsonl'), last('f6/campaign/recheck_new.jsonl')
ver  = sum(new[c]['status'] == 'verified' for c in new)
cnf  = sum(new[c].get('cnf_sha256')  == old[c].get('cnf_sha256')  for c in new)
lrat = sum(new[c].get('lrat_sha256') == old[c].get('lrat_sha256') for c in new)
print(f'cubes={len(new)} verified={ver} cnf_sha256_equal={cnf} lrat_sha256_equal={lrat}')
EOF
```

Expected, as in `f6/campaign/recheck_2026-09-09.txt`: 205 / 205 verified,
205 / 205 `cnf_sha256` equal, 204 / 205 `lrat_sha256` equal (on arm64; the
one difference is a container-origin record whose proof trace differs
across architectures). The CNF hashes must always match: they say the
formula you solved is the formula the campaign solved. The LRAT hashes
reproduce only with a bit-identical solver build; a mismatch there is a
different proof of the same formula, and the verdict is what counts. The
run took 263 s wall with 6 workers on an M4 laptop.

Any other cubes can be passed the same way (`--cubes`, ids from
`all_ids.txt` of 3.4). Re-solving the whole tree is about 300 core-hours
of solver time plus checking; `f6/CAMPAIGN.md` describes the splitting
rules, so a full re-run can follow the same tree (`--cubes` over
`verified.txt`) or grow its own from the roots.

Corroboration, not evidence: an earlier exhaustive enumeration of all
schedules (`f6/exploration/gen_enum.c`; rebuild with
`cc -O2 -o gen_enum_c f6/exploration/gen_enum.c`) also gives a maximum
of 48.

### 3.8 Replaying every module through the kernel (leanchecker, ~5 min)

Lean 4.33.1 ships `leanchecker`, which loads the `.olean` files and
replays every declaration of a module through the kernel; it prints
nothing and exits 0 when all are accepted. Recorded run:
`f6/campaign/leanchecker_2026-09-09.txt` (38 / 38 modules clean).

```bash
cd lean/SmpF5
for m in $(grep -oE '^import SmpF5\.\w+' SmpF5.lean | sed 's/import //') SmpF5; do
  lake env leanchecker $m || echo FAIL $m
done                                          # expect no output; about 8 s per module
lake env leanchecker SmpF5.DoesNotExist       # negative control: must error (the tool is live)
```

## 4. f(5) = 16 in full

The theorem is `f5_eq_16_of_unsat` in `lean/SmpF5/SmpF5/Lower.lean`:

```
(∀ row ∈ perms120, ¬Satisfiable (cubeCNF row)) →
  (∀ I : Inst, WF I = true → stableCount I ≤ 16) ∧ ∃ I, WF I = true ∧ stableCount I = 16
```

IF the 120 cube formulas are unsatisfiable THEN f(5) = 16: the upper bound
for every well-formed instance and an embedded witness with exactly 16,
in one statement over one `stableCount`. Total cost: about half an hour
of reading and 2–3 hours of unattended compute.

### Step 1 — check the Lean development (~20 min machine time)

Fast-path steps 1 to 3 already did this; the f(5)-specific commands are:

```bash
cd lean/SmpF5
lake exe cache get      # prebuilt Mathlib (or build from source if paranoid)
lake build              # kernel-checks every theorem; must end with no errors
grep -rn sorry SmpF5/   # must print nothing
printf 'import SmpF5.Lower\n#print axioms f5_eq_16_of_unsat\n' > ax5.lean
lake env lean ax5.lean  # 'f5_eq_16_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
lake env lean ../Witness.lean     # the witness standalone, kernel-only: depends on axioms: [propext]
```

### Step 2 — read the definitions (~30 min, human)

Read, in this order (all under `lean/SmpF5/`):

- `SmpF5/Faithful.lean` — `Inst`, `isRankRow`, `WF`, `isStable`,
  `stableCount` (the mathematical content, about 40 lines);
- the statement (not proof) of `f5_upper_of_unsat` in `SmpF5/Bridge.lean`;
- `SmpF5/Encoding.lean` — `cubeCNF` and `Satisfiable` (you need not
  understand the encoding; the theorem quantifies over it);
- `ExportCnf.lean` — the printer.

### Step 3 — regenerate and refute the 120 formulas (~2–3 h unattended)

Tools: kissat 4.0.4 on `PATH` (build from
[arminbiere/kissat](https://github.com/arminbiere/kissat), release 4.0.4:
`./configure && make`), drat-trim built into `dt-src/` at the clone root
(`git clone https://github.com/marijnheule/drat-trim.git dt-src && make -C dt-src`;
we used commit `2e3b2dc`), and the cake_lpr of section 3.5 in
`cake_lpr-src/`. Any other DRAT/LRAT-producing solver and any checker you
trust can be substituted.

```bash
cd lean/SmpF5
lake build export_cnf
mkdir -p cubes && cd cubes
../.lake/build/bin/export_cnf
```

This writes 240 DIMACS files **from the Lean definitions** into
`lean/SmpF5/cubes/`: the 120 production cubes `cubeL000.cnf` ..
`cubeL119.cnf` and 120 positive controls `cubeL16_000.cnf` ..
`cubeL16_119.cnf` (the same cubes at 16 slots; see the cross-checks
below). For reference, our export hashes to

```
cat cubeL*.cnf | shasum -a 256            # all 240 files
a93f5e58cd23976b303e26f5dd2fcd4ab66f91797b0b02bd2bfba13887c6a2ef
cat cubeL[01][0-9][0-9].cnf | shasum -a 256   # the 120 production files only
044d0edbd9762166d925038056b3ef9ed762293d3f7637055e1105d1eca30ec6
```

but you need not compare: you generated your own copies. Now refute each
and check each proof, still in `lean/SmpF5/cubes/` (`../../..` is the
clone root):

```bash
DT=../../../dt-src/drat-trim
CAKE=../../../cake_lpr-src/cake_lpr
for i in $(seq -f '%03g' 0 119); do
  kissat -q cubeL$i.cnf cubeL$i.drat                 # expect exit 20 (UNSAT)
  $DT cubeL$i.cnf cubeL$i.drat -L cubeL$i.lrat       # expect "s VERIFIED"
  $CAKE cubeL$i.cnf cubeL$i.lrat                     # expect "s VERIFIED UNSAT"
  rm cubeL$i.drat cubeL$i.lrat                       # ~0.5 GB per cube otherwise
done
```

All 120 must report UNSAT + VERIFIED. Our run's log is
`f5/cubesL/cubesL_results.txt` (sha256
`200062889de4aea7ab5e15b959fed8367dd62c6eeddac319a43d70be7c3dccb9`;
`f5/cubesL/run_one.sh` is the per-cube script it was produced with), kept
for reference only: your own run supersedes it.

Together with Step 1 this discharges the hypothesis of
`f5_upper_of_unsat`: **f(5) ≤ 16**, hence with the witness, **f(5) = 16**.

### Optional cross-checks

- Positive control: `cubeL16_105.cnf` (16 slots, the cube containing the
  known extremal instance) must be **SAT**, which guards against encodings
  that are vacuously unsatisfiable.
- `python3 smp.py` validates the independent brute-force counter against
  four known extremal instances from OEIS A351413 (3/10/9/48).
- Independent earlier refutations of "≥ 17" with a different encoding and
  solver configurations are recorded in `docs/history/NOTES.md`.

## 5. What is and is not a theorem

For f(5), `f5_eq_16_of_unsat` makes the 120 certificates the only
hypothesis of a kernel-checked statement; for f(6), `f6_eq_48_of_unsat`
does the same with the certified cube formulas of `finalCubes` (the
faithfulness theorem — every well-formed order-6 instance with ≥ 49
stable matchings yields a satisfying assignment of some certified cube's
formula — is `cube_faithful6` composed with `exists_canonical_schedule`
and `fits_final`). Everything from the definitions to that hypothesis is
a Lean theorem. What is not a theorem is the hypothesis itself: it is
discharged by the checker verdicts recorded in the self-attested journal,
as described in section 0, exactly as f(5)'s hypothesis is discharged by
the log of the 120 cake_lpr runs.

## 6. Known gaps (state of 2026-09-09)

- f(5): LRAT certificates are not archived (regenerable in about 2 h;
  a Zenodo archive with DOI is planned so verifiers can skip solving and
  only re-check). f(6): the certificates (about 25 TB) were not kept; see
  item 6 of section 0.
- f(6): the journal's verdicts have been independently reproduced for a
  205-cube sample (3.7), not for the whole tree (about 300 core-hours);
  a third-party re-check by someone other than the author is the next
  item in `STATUS.md`.
- cake_lpr's binary hash was not recorded per journal record; the driver
  records the checker's path in the journal header, and the assembly
  hashes of the two builds are asserted in `f6/CAMPAIGN.md` and
  re-checked in the sample re-solve.

## 7. Appendix: the 25 theorems CI checks

Definitions to read first: `Inst6`, `WF6`, `isStable6`, `stableCount6`,
`stab`, `readoff` at the top of `SixBridge.lean` (same style as the
order-5 ones); `readoffS`, `Legal` in `Sched6.lean`. All files are under
`lean/SmpF5/SmpF5/`.

- `bridge` (SixBridge.lean): for well-formed order-6 `I`,
  `stableCount6 I <= stableCount6 (readoff I)` — the bridge lemma;
- `chain_complete`, `traj_mem_iff`, `wtraj_nodup`, `total_moves_le_30`
  (Lattice6.lean, Chain6.lean): the validity layer — an explicit maximal
  chain from the man-optimal to the woman-optimal stable matching whose
  trajectories are exactly the stable partners in preference order,
  without repetition, within the total budget of 30 moves (the closing
  docstring of `Chain6.lean` maps every clause to its theorem);
- `count_le_of_orderPreserving` (AbsBridge6.lean): the bridge in
  bottom-agnostic form;
- `sc_le_readoffS_chainSched` (ValidityBridge6.lean), `manOpt_wrelabel6`
  (WRelabel6.lean) and, unconditionally, **`validity_unconditional`**
  (WRelabel6.lean): for every well-formed order-6 instance `I` there is a
  `Legal` schedule `S` with `stableCount6 I <= stableCount6 (readoffS S)`
  — the composed Validity + Bridge statement (`readoffS`/`Legal` are the
  read-off instance and schedule legality of Definitions 1–2: bottom
  completion in ascending label order, women's trajectories reversed);
- `Legal_length_le_15` (SchedLen6.lean): a legal schedule has at most 15
  steps — the frame bound that fixes the size of the formula;
- `Legal_map_minFirst` and `minFirst_mem_cyclicShapes` (Shapes6.lean):
  rotating every step to start at its smallest man preserves legality,
  and every such step is an entry of the campaign's shape table;
- `permsN6_perm_permutations` (Shapes6.lean): the list of 720
  permutations over which the formula counts stable matchings is a
  permutation of Mathlib's `permutations` of the identity row;
- `PM_sem`, `PW_sem` (ReadoffSem6.lean): for a legal schedule of at most
  15 steps, the formula's man-side and woman-side preference gates
  (`PM`, `PW`) agree with the ranks of the read-off instance — the
  read-off semantics of the encoding;
- `SchedCNF6.dec_pwVar3` (Decode6.lean): the last of the decode-layer
  lemmas — the decoder `dec6` inverts the variable layout (here on the
  woman-side gate variables `pwVar … 3`);
- `Legal_relabel`, `sc_le_readoffS_relabelSched` (RelabelSched6.lean) and
  `firstApp_relabel` (FirstApp6.lean): relabeling men and women by the
  first-participation order keeps a schedule legal, makes it canonical
  (the new men of each step are the next unused labels), and does not
  lower the read-off count — the count bridge is re-instantiated at the
  relabeled instance, since the read-off itself is not
  relabel-equivariant;
- `exists_canonical_schedule` (Faithfulness6.lean): from an instance with
  ≥ 49 stable matchings to a legal, canonical schedule whose read-off has
  ≥ 49;
- `fits_final` (Coverage6.lean): every legal canonical schedule fits some
  cube of `finalCubes` (the certified cube set);
- `cube_faithful6` (Faithfulness6.lean): the schedule's natural
  assignment satisfies the formula of any well-formed cube it fits, when
  its read-off has ≥ 49 stable matchings — the faithfulness theorem, the
  analogue of f(5)'s `cube_faithful`;
- `dihedral6_count` (Lower6.lean): the witness;
- `f6_upper_of_unsat`, `f6_eq_48_of_unsat` (Bridge6.lean): the assembly.

The first nine are the reduction layer proper; the other sixteen are the
faithfulness layer (complete as of 2026-09-08; `STATUS.md`).
