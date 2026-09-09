# Order-6 campaign reference

The completed run is archived in
[results/f6/campaign-2026-09-08](../../results/f6/campaign-2026-09-08/README.md).
This page documents current commands. [Historical development notes](../history/f6-campaign-development.md)
record old probes, commands, timings, and operational decisions.

Run commands from the repository root. Live output defaults to `runs/f6/`;
completed artifact journals should remain immutable.

## Toolchain

The production run used CaDiCaL 3.0.1 at
`c60730422e758ef1cebe7aeddf2dda31c996bf04`, with native textual LRAT,
followed by cake_lpr at `a36874a`. The [toolchain guide](solver-toolchain.md)
gives the full assembly hashes, build commands and self-test for ARM64
and Linux/x86-64, plus the recorded sample re-solve.

Build [CaDiCaL](https://github.com/arminbiere/cadical) at that commit and
[cake_lpr](https://github.com/tanyongkiam/cake_lpr) for your platform. The
driver expects `cadical-src/build/cadical` and `cake_lpr-src/cake_lpr`
under the repository root. `SMP_TOOLCHAIN_ROOT` can point to another
directory containing those source/build folders. Run upstream self-tests
before starting a campaign. The alternative kissat path additionally needs
`dt-src/drat-trim` and kissat on PATH.

## Count, audit, or regenerate

```bash
python3 -m tools.campaign.cube_campaign --count
mkdir -p runs/f6
gzip -dc results/f6/campaign-2026-09-08/campaign.jsonl.gz > runs/f6/campaign.jsonl
python3 -m tools.campaign.cube_campaign --audit --journal runs/f6/campaign.jsonl
```

Expected root count: 25,493 (25,339 open depth-2 prefixes and 154 stopped
shorter prefixes). The audit verifies the base formula identity, recorded
verdict fields, and recursive coverage of every root. It does not read
certificate contents. Encoder source-hash notices are provenance checks
and are reported separately from formula mismatches.

To regenerate one cube into a fresh journal:

```bash
python3 -m tools.campaign.cube_campaign --solver cadical --workers 1   --cubes '0,1;2,3' --time 3600 --check-timeout 14400   --journal runs/f6-sample/campaign.jsonl --scratch runs/f6-sample/scratch
```

A sample journal intentionally fails a full-coverage audit. To regenerate
the full campaign, use a fresh journal and omit `--cubes`:

```bash
python3 -m tools.campaign.cube_campaign --solver cadical --workers 4   --time 300 --max-depth 4 --shuffle   --journal runs/f6-new/campaign.jsonl --scratch runs/f6-new/scratch
```

Choose workers to fit available memory and disk. The base file is about
48.7 MB; historical LRAT proofs reached 9.8 GB. The campaign streams proof
deletion after checking. Use `--keep-failures` to retain unsuccessful cases.
Adaptive splitting may leave cases at the maximum depth to retry with
larger limits; completion is determined by the final audit, not elapsed time.

## Resume, inspect, retry

Rerun the same command with the same live journal to resume. One driver
holds the journal lock at a time. Progress and retry examples:

```bash
python3 -m tools.campaign.cube_campaign --summary --journal runs/f6-new/campaign.jsonl
python3 -m tools.campaign.cube_campaign --solver cadical --workers 4   --retry-status timeout_maxdepth,error,cake_fail,check_timeout   --time 3600 --check-timeout 14400 --lrat-split-mb 12000   --journal runs/f6-new/campaign.jsonl --scratch runs/f6-new/scratch
python3 -m tools.campaign.cube_campaign --audit --journal runs/f6-new/campaign.jsonl
```

The dashboard is read-only with respect to the journal:

```bash
python3 -m tools.campaign.dashboard --journal runs/f6-new/campaign.jsonl   --scratch runs/f6-new/scratch --log runs/f6-new/campaign.log
```

The log option should point to captured driver output when one is available.
Use each tool's `--help` for all flags. The driver defaults to kissat for
compatibility; the examples explicitly select the production CaDiCaL path.

## Formula identity and Lean exports

The complete identity check rebuilds the base formula, root and split lists,
final cube set and unit clauses, then compares every journaled formula hash:

```bash
python3 tools/campaign/check_lean_identity.py --journal runs/f6/campaign.jsonl
```

Expected: 318,736 final leaves and 321,492 matching formula hashes. This
checks the formulas; it does not re-check the deleted certificates. See the
[verification guide](../verification.md) for the complete evidence chain.

The base formula and each cube's CNF hash are separate identities. Export
root and split-child lists with `export_cubes6`. Its `--parents=FILE`
argument takes one split-parent cube ID per line and emits tab-separated
parent/child pairs.

With `--expect-cnf-dir DIR`, the audit regenerates Python CNFs and compares
their hashes with the journal. If `DIR/c_<cube_tag(id)>.cnf` already exists,
it also compares that external file. To compare Lean, first export Lean
CNFs under those exact names; use `parse_cube_id` and `cube_tag` from
[cube_campaign.py](../../tools/campaign/cube_campaign.py). A missing external
file is not itself an audit failure, so independently check that the
external file inventory covers the intended cube set. This operation
does not recheck certificates.

## Journal records and provenance

The first record is a header with formula dimensions, `base_sha256`, source
hash, and toolchain information. Cube records contain `cube`, `prefix`,
`closed`, `depth`, `status`, and subprocess results. A verified record
requires solver exit 20, cake_lpr exit 0 with `s VERIFIED UNSAT`, no killed
process flags, and well-formed `cnf_sha256` / `lrat_sha256` fields.

`split` records delegate coverage to all generated children. SAT records
retain a decoded model and independent recount information for investigation.
The append-only journal can contain repeated attempts; the audit resolves
the effective record per cube. Retain its original field names and cube IDs.

## Shards and optional cloud backend

`--shard I/N` deterministically assigns roots and their descendants to a
shard. Merge separate journals with
[merge_journals.py](../../tools/campaign/merge_journals.py), then audit the result.

The optional [Modal driver](../../tools/campaign/run_modal.py) uses the same
worker and journal format. It packages the `tools` Python package and sets
`SMP_TOOLCHAIN_ROOT=/` in its image. Install and authenticate Modal only if
you intend to use that backend; review its current resource pricing and
the driver's budget flags before launching. The archived container
checkpoint scripts in [history](../history/container-scripts/README.md)
describe a retired setup and are not current launch commands.

The [archived 2026-09-09 reference](../history/campaign-reference-2026-09-09.md)
retains detailed provenance and operational observations from the original run.
