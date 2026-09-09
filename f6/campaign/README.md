# f6/campaign: the certificate-campaign evidence

The files at the top of this directory are the evidence for the hypothesis
of `f6_eq_48_of_unsat`; `tools/` and `probes/` are how the campaign was run.
Numbers: `../../STATUS.md`; details: `../CAMPAIGN.md`. The dated transcripts are kept byte for byte.

| file | what it is |
|---|---|
| `campaign.jsonl.gz` | the journal, sha256 `c9026b08045d8e8824c66d213bfa8eeb5336f118c22e030d42040136be7a8e4e`: gzipped append-only JSONL, one header (base-formula sha256, tool paths) then one or more records per cube; **the last record per cube wins**. Every `verified` record carries `cnf_sha256` (hashed before solving) and `lrat_sha256` (hashed before checking); it is the driver's transcription of cake_lpr's verdict, the certificate itself was deleted |
| `audit_final.txt` | transcript of `cube_campaign.py --audit` on the final journal: every root covered, no bad records, `audit: OK`, exit 0 |
| `audit_mainrun.txt` | the audit before the final rerun of the depth-4 cubes that had hit the LRAT cap: `FAILED`, those cubes listed as `timeout_maxdepth`; superseded by `audit_final.txt`, kept to show what the rerun closed |
| `lean_identity.txt` | 2026-09-08 transcript: base formula, root cubes, split children, `finalCubes` and every journaled formula hash re-derived from the Lean definitions |
| `recheck_2026-09-09.txt`, `recheck_2026-09-09.jsonl` | independent re-solve of a random sample of certified cubes on a second machine with the toolchain rebuilt from source: commands, hashes and times, and the fresh journal it produced |
| `leanchecker_2026-09-09.txt` | Lean's `leanchecker` replayed every module of the development through the kernel: all clean |

## tools/ (operations)

| file | role |
|---|---|
| `tools/driver.cmd` | the one-line driver command the supervisor relaunches |
| `tools/supervise.sh` | reboot-proof relaunch of the driver and the checkpoint loop in the Linux container |
| `tools/snapshot.sh` | hourly checkpoint: gzip the journal under its own lock, commit, push |
| `tools/bootstrap.sh` | bare container to running shard: builds CaDiCaL at the pinned commit and cake_lpr from its hash-checked assembly, self-tests both, seeds and pushes the shard journal |
| `tools/dashboard.py`, `tools/dashboard.html` | read-only live dashboard that tails the journal |

## probes/ (pilot runs, 2026-09-02 to 09-05)

| file | what it recorded |
|---|---|
| `probes/dryrun.jsonl`, `probes/dryrun.log` | the first dry run with the kissat + drat-trim chain; pre-provenance records (no `cnf_sha256`), so `--audit` rejects them by design |
| `probes/fixcheck.jsonl` | the hardened driver on three easy cubes: header, hashes, retry and lock behaviour |
| `probes/cadical_check.jsonl`, `probes/cadical_check.log` | the same three cubes with `--solver cadical`; their `lrat_sha256` equal the main run's |
| `probes/cadical_hard.jsonl`, `probes/cadical_hard.log` | the hard cube `0,1;2,3` under cadical: split into children at the time limit |
| `probes/depth3_probe.jsonl`, `probes/depth3_probe.log` | the depth-3 pricing probe on a uniform sample of split children |
| `probes/depth3_count.log` | count of rule-(a) canonical depth-3 prefixes |

## Decompress and audit

    cd f6
    gunzip -k campaign/campaign.jsonl.gz                                  # campaign.jsonl is gitignored
    python3 cube_campaign.py --audit --journal campaign/campaign.jsonl    # expect "audit: OK", exit 0
    python3 cube_campaign.py --summary --journal campaign/campaign.jsonl

The audit recomputes the base formula and the root set, checks that every
root is `verified` or `split` with all children covered, and checks every
verified record's fields; it is a consistency check of the journal, not a
re-check of any certificate. Re-checking a verdict means re-solving the cube
from the Lean-printed formula (`../../VERIFYING.md`; `recheck_2026-09-09.txt`
has the exact command). The driver's raw stdout (`campaign.log`) is not
tracked; the container fan-out record is `../../docs/history/f6-campaign-FANOUT.md`.
