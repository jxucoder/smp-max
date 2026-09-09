# Verifying f(5) = 16 and f(6) = 48 from scratch

This guide lets a third party check every link of the evidence chain on
their own machine, **without trusting any run we performed**. For f(5)
the total cost is about half an hour of reading and 2–3 hours of
unattended compute (Steps 1–3). For f(6) (sections after the optional
cross-checks) the Lean build, the journal audit and the Lean identity
checks take minutes; re-solving the whole certificate campaign, which is
what "without trusting any run we performed" means for that layer,
costs about 300 core-hours.

## What you end up trusting (and nothing else)

1. **Lean 4's kernel** (small, independently re-implementable; you can
   additionally replay every module through the kernel with Lean's
   `leanchecker`, see the f(6) section).
2. **Three standard axioms**: `propext`, `Classical.choice`, `Quot.sound`
   (`Witness.lean` needs only `propext`).
3. **~40 lines of definitions** (`Inst`, `WF`, `isStable`, `stableCount`
   in `f5/lean/SmpF5/SmpF5/Faithful.lean`) — YOU must read these and
   agree they say "5×5 stable-marriage instance" and "number of stable
   matchings". This is the one irreducibly human step.
4. **One LRAT proof checker of your choice.** We used cake_lpr, whose
   correctness is itself machine-checked down to machine code; you may
   substitute any checker (drat-trim, lrat-check, verified Coq/Lean
   checkers). Checker diversity replaces trust.
5. The ~30-line DIMACS printer `ExportCnf.lean` (read it, or bypass it by
   printing the Lean terms yourself).

For f(6) the list is the same, item for item: in item 3 the definitions
are `Inst6`, `WF6`, `isStable6`, `sms6`, `stableCount6` at the top of
`f5/lean/SmpF5/SmpF5/SixBridge.lean` (about 40 lines); in item 5 the
printers are `ExportSchedCnf.lean` and `ExportCubes6.lean`; and the
campaign journal enters as described under "What the certificate layer
does and does not establish" below.

Not on the list: our solver runs, our Python scripts, our honesty.

## Step 1 — check the Lean development (~20 min machine time)

```bash
git clone <this repo> && cd smp-max/f5/lean/SmpF5
lake exe cache get      # prebuilt Mathlib (or build from source if paranoid)
lake build              # kernel-checks every theorem; must end with no errors
```

Confirm no hidden holes and the exact axiom base of the main theorem
(upper and lower bound combined):

```bash
echo 'import SmpF5.Lower
#print axioms f5_eq_16_of_unsat' > /tmp/ax.lean && lake env lean /tmp/ax.lean
```

Expected output (nothing else):

```
'f5_eq_16_of_unsat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Also check the lower-bound witness (standalone, kernel-only):

```bash
lake env lean ../Witness.lean     # prints: depends on axioms: [propext]
```

`grep -rn sorry SmpF5/` must return nothing.

What this buys you: **IF the 120 cube formulas are unsatisfiable THEN
f(5) = 16** (`f5_eq_16_of_unsat`: the upper bound for every well-formed
instance AND an embedded witness with exactly 16, in one statement over
one `stableCount`), as a machine-checked theorem over the definitions
you read in item 3 above. `Witness.lean` re-proves the witness count
standalone using only `propext`.

## Step 2 — read the definitions (~30 min, human)

Read, in this order:
- `SmpF5/Faithful.lean` — `Inst`, `isRankRow`, `WF`, `isStable`,
  `stableCount` (the mathematical content, ~40 lines);
- the statement (not proof) of `f5_upper_of_unsat` in `SmpF5/Bridge.lean`;
- `SmpF5/Encoding.lean` — `cubeCNF` and `Satisfiable` (you need not
  understand the encoding; the theorem quantifies over it);
- `ExportCnf.lean` — the printer.

## Step 3 — regenerate and refute the 120 formulas (~2–3 h unattended)

```bash
lake build export_cnf
mkdir -p /tmp/cubes && cd /tmp/cubes
<repo>/f5/lean/SmpF5/.lake/build/bin/export_cnf
```

This writes 240 DIMACS files **from the Lean definitions**: the 120
production cubes `cubeL000.cnf` .. `cubeL119.cnf` and 120 positive
controls `cubeL16_000.cnf` .. `cubeL16_119.cnf` (the same cubes at 16
slots; see the cross-checks below). For reference, our export hashes to

```
cat cubeL*.cnf | shasum -a 256            # all 240 files
a93f5e58cd23976b303e26f5dd2fcd4ab66f91797b0b02bd2bfba13887c6a2ef
cat cubeL[01][0-9][0-9].cnf | shasum -a 256   # the 120 production files only
044d0edbd9762166d925038056b3ef9ed762293d3f7637055e1105d1eca30ec6
```

but you need not compare — you generated your own copies.

Now refute each with any DRAT/LRAT-producing solver and check each proof
with any checker you trust. Our loop (kissat 4.0.4, drat-trim @2e3b2dc,
cake_lpr @a36874a, built from their public sources):

```bash
for i in $(seq -f '%03g' 0 119); do
  kissat -q cubeL$i.cnf cubeL$i.drat            # expect exit 20 (UNSAT)
  drat-trim cubeL$i.cnf cubeL$i.drat -L cubeL$i.lrat   # expect "s VERIFIED"
  cake_lpr cubeL$i.cnf cubeL$i.lrat             # expect "s VERIFIED UNSAT"
  rm cubeL$i.drat cubeL$i.lrat                  # ~0.5GB per cube otherwise
done
```

All 120 must report UNSAT + VERIFIED. Our run's log is
`f5/cubesL/cubesL_results.txt` (sha256
`200062889de4aea7ab5e15b959fed8367dd62c6eeddac319a43d70be7c3dccb9`),
kept for reference only — your own run supersedes it.

Together with Step 1 this discharges the hypothesis of
`f5_upper_of_unsat`: **f(5) ≤ 16**, hence with the witness, **f(5) = 16**.

## Optional cross-checks

- Positive control: `cubeL16_105.cnf` (16 slots, the cube containing the
  known extremal instance) must be **SAT** — guards against encodings
  that are vacuously unsatisfiable.
- `python3 smp.py` validates the independent brute-force counter against
  four known extremal instances from OEIS A351413 (3/10/9/48).
- Independent earlier refutations of "≥17" with a different encoding and
  solver configs live in the results log of the root `README.md`.

## Verifying f(6) = 48

f(6) = 48 has three layers with different trust levels (top-level
`README.md`): the Lean reduction (theorems), the certificate campaign
(an audited journal plus Lean identity checks), and the faithfulness
theorem (see `STATUS.md`). The lower bound is the dihedral instance
(`f6/README.md`; `python3 smp.py` recounts it in seconds).

### The theorem (Lean, ~1 min on top of Step 1)

The same `lake build` also kernel-checks the order-6 development. Its
end statement is `f6_eq_48_of_unsat` (`SmpF5/Bridge6.lean`):

```bash
echo 'import SmpF5.Bridge6
#print axioms f6_eq_48_of_unsat
#check @f6_eq_48_of_unsat' > /tmp/ax6main.lean && lake env lean /tmp/ax6main.lean
```

Expected: `'f6_eq_48_of_unsat' depends on axioms: [propext,
Classical.choice, Quot.sound]` and the statement

```
(∀ c ∈ Cubes6.finalCubes, ¬Satisfiable (Cubes6.cubeFormula 49 c)) →
  (∀ (I : Inst6), WF6 I = true → stableCount6 I ≤ 48) ∧ ∃ I, WF6 I = true ∧ stableCount6 I = 48
```

Read as: IF every cube formula of the certified cube set is
unsatisfiable THEN f(6) = 48 (upper bound for every well-formed order-6
instance, and the dihedral witness with exactly 48, `dihedral6_count`,
kernel-computed in `Lower6.lean`). `Cubes6.finalCubes` and
`Cubes6.cubeFormula` are Lean definitions; the identity checks below show
that they are exactly the cubes and formulas the campaign refuted.

### The 25 theorems CI checks (~5 min)

Check the axiom base of the theorems that CI checks
(`.github/workflows/lean-verify.yml`):

```bash
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
#print axioms f6_eq_48_of_unsat' > /tmp/ax6.lean && lake env lean /tmp/ax6.lean
```

All 25 must report `[propext, Classical.choice, Quot.sound]`. What they
say (definitions to read: `Inst6`, `WF6`, `isStable6`, `stableCount6`,
`stab`, `readoff` at the top of `SixBridge.lean`, same style as the
order-5 ones; `readoffS`, `Legal` in `Sched6.lean`):

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

### The certificate campaign: audit and Lean identity checks (~10 min)

The upper bound's second layer is the refutation of "some legal
schedule reads off ≥ 49": the Lean-defined formula
`SchedCNF6.schedCNFn 6 49` (84,882 variables, 2,709,212 clauses) was
refuted over a tree of cubes — 25,493 root cubes (`Cubes6.canonicalCubes2`),
321,492 distinct cubes after splitting, 318,736 of them refuted by
CaDiCaL 3.0.1 (`--lrat --binary=false`) with the certificate accepted by
cake_lpr, 2,756 split (1,804 at depth 2, 952 at depth 3), 0 satisfiable
(`f6/CAMPAIGN.md`). The journal `f6/campaign/campaign.jsonl.gz`
(40,943,262 bytes) has one record per attempt; the last record per cube
wins. Reference hash:

```
shasum -a 256 f6/campaign/campaign.jsonl.gz
c9026b08045d8e8824c66d213bfa8eeb5336f118c22e030d42040136be7a8e4e
```

**Audit** (checks that every root cube is verified or split with all
children recursively covered, that the header's base formula hash
equals the recomputed formula, and that every `verified` record has
solver rc 20, `cake_verified`, no kill flag and well-formed hashes):

```bash
gunzip -k f6/campaign/campaign.jsonl.gz
python3 f6/cube_campaign.py --audit --journal f6/campaign/campaign.jsonl
# expect: audit: roots=25493 nodes=321492 verified=318736 missing=0 bad=0 header_problems=0
#         audit: OK   and exit status 0
```

**Lean identity checks** (recorded in `f6/campaign/lean_identity.txt`;
they establish that what the campaign solved is exactly what the Lean
definitions denote). First extract the id lists from the journal, last
record per cube:

```python
import json
last = {}
for line in open('f6/campaign/campaign.jsonl'):
    r = json.loads(line)
    if 'cube' in r and 'status' in r:
        last[r['cube']] = r                      # last record per cube wins
w = lambda name, ids: open(name, 'w').write(''.join(i + '\n' for i in ids))
w('all_ids.txt', last)                                                  # 321,492
w('verified.txt', [c for c, r in last.items() if r['status'] == 'verified'])  # 318,736
w('split_ids.txt', [c for c, r in last.items() if r['status'] == 'split'])    # 2,756
```

Then, from `f5/lean/SmpF5` (paths to the three files above as needed):

```bash
lake build export_sched_cnf export_cubes6
.lake/build/bin/export_sched_cnf base.cnf          # the base formula; sha256 28421fb6…
.lake/build/bin/export_cubes6 roots.txt            # Cubes6.canonicalCubes2: 25,493 ids
.lake/build/bin/export_cubes6 children.tsv --parents=split_ids.txt   # extendCanon: 295,999 parent/child lines
.lake/build/bin/export_cubes6 final.txt --final    # Cubes6.finalCubes: the certified cube set
sort final.txt > a; sort verified.txt > b; cmp a b && wc -l a         # identical, 318,736 lines
.lake/build/bin/export_cubes6 units.tsv --units=all_ids.txt          # each cube's unit clauses (~150 s)
python3 ../../../f6/lean_rehash.py base.cnf units.tsv ../../../f6/campaign/campaign.jsonl
# expect: lean_rehash: records with cnf_sha256=321492 matched=321492 mismatched=0 missing_units=0
#         and exit status 0
```

What each line shows: `base.cnf` is byte-identical to the campaign's
base formula (sha256 `28421fb68b0f494b99d1918aa64cff248443161dc7a6c220e0c3e895a67df59b`,
the journal header's `base_sha256`); `roots.txt` equals the driver's
root list; `children.tsv` equals the driver's children of every cube
that was split; `final.txt` — the Lean-defined `finalCubes`
(`SplitList6.lean`: `refineCubes` of `canonicalCubes2` by the 1,804 +
952 recorded split ids) — equals the set of verified ids; and every one
of the 321,492 journaled `cnf_sha256` values (hashed by the driver
before solving) recomputes from the Lean-printed header, body and unit
clauses. Any single cube can also be printed in full: an open cube with
id `0,1;2,3` is `export_sched_cnf OUT --prefix='0,1;2,3'`; a closed cube
whose id ends in `;stop`, say `0,4,2,3,5,1;stop`, is
`export_sched_cnf OUT --prefix='0,4,2,3,5,1' --stop`; the root cube
`stop` is `export_sched_cnf OUT --stop` alone. Quote the argument — the
ids contain semicolons. The file's sha256 must equal that cube's
journaled `cnf_sha256`.

### What the certificate layer does and does not establish

The journal is self-attested. A `verified` record is the driver's
transcription of cake_lpr's verdict (`s VERIFIED UNSAT`, exit 0) for
that cube; the certificates (about 25 TB in total) were deleted after
checking, and the audit checks the records' consistency, not the
certificates. Three machines produced the records: a Linux/x86-64
container (3,967 verified + 235 split, checked by the x86-64 cake_lpr
build, `cake_lpr.S` sha256 `2f3af32d…`), an Apple M4 Max laptop (12,727
+ 628) and a Mac mini M4 Pro (302,042 + 1,893; arm64 build,
`cake_lpr_arm8.S` sha256 `95b64883…`); one solver build throughout
(CaDiCaL 3.0.1 c6073042).

To verify a verdict independently, re-solve the cube: print its formula
from Lean as above (the sha256 must match the record's `cnf_sha256`),
refute it with any LRAT-producing solver, and check the certificate with
cake_lpr or any checker you trust. The per-cube `cnf_sha256` and
`lrat_sha256` let a re-run be compared with the journal record by
record (the LRAT hash reproduces only with a bit-identical solver; the
CNF hash always must). Re-solving the whole tree is about 300 core-hours
of solver time (1,076,400 s in our run, median 1.0 s per cube, a few
cubes hours) plus checking; `f6/cube_campaign.py` is the driver we used,
and `f6/CAMPAIGN.md` describes the splitting rules, so a re-run can
follow the same tree or its own.

Corroboration, not evidence: an earlier exhaustive enumeration of all
26,574,282,886 schedules (`f6/gen_enum.c`) also gives a maximum of 48.

### What is and is not a theorem

For f(5), `f5_eq_16_of_unsat` makes the 120 certificates the only
hypothesis of a kernel-checked statement; for f(6), `f6_eq_48_of_unsat`
does the same with the 318,736 certified cube formulas (the faithfulness
theorem — every well-formed order-6 instance with ≥ 49 stable matchings
yields a satisfying assignment of some certified cube's formula — is
`cube_faithful6` composed with `exists_canonical_schedule` and
`fits_final`). Everything from the definitions to that hypothesis is a
Lean theorem. What is not a theorem is the hypothesis itself: it is
discharged by the checker verdicts recorded in the self-attested journal,
as described above, exactly as f(5)'s hypothesis is discharged by the log
of the 120 cake_lpr runs.

## Known gaps (state of 2026-09-09)

- f(5): LRAT certificates are not archived (regenerable in ~2 h; a
  Zenodo archive with DOI is planned so verifiers can skip solving and
  only re-check). f(6): the certificates (about 25 TB) were not kept;
  see the trust statement above.
- `leanchecker` (Lean's built-in kernel re-checker) was run over every
  module on 2026-09-09: 38 / 38 modules clean, 0 failures
  (`f6/campaign/leanchecker_2026-09-09.txt`). To repeat:
  `cd f5/lean/SmpF5 && for m in $(grep -oE '^import SmpF5\.\w+' SmpF5.lean | sed 's/import //'); do lake env leanchecker $m || echo FAIL $m; done`
  (silent exit 0 per module means every declaration replayed through the
  kernel; about 8 s per module).