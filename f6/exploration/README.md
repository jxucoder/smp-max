# f6/exploration: corroboration, not evidence

Nothing in this directory is on the evidence path for f(6) = 48; that
path is the Lean theorem plus `../campaign/` (`../../STATUS.md`). These
are the searches, enumerations and abandoned encodings of the 2026-08-31
to 09-05 attack (`../../docs/history/f6-ATTACK_LOG.md`). Every search
here tops out at 48, independently of the certificates.

| file | what it was | what it corroborates |
|---|---|---|
| `hillclimb.py`, `hillclimb_round1.log` | local search over raw 6 x 6 instances (exact counting), from the dihedral instance and random restarts, 8 seeds | no instance above 48 found in instance space |
| `struct_hunt.py`, `struct_hunt_round1.log` | search over full-budget swap schedules (15 transpositions), the space the reduction later formalized | no schedule above 48 found |
| `relaxed_search.py` | relaxation of the full-budget regime: maximize downsets of the closure of the 12 per-person chains in the rotation poset | the full-budget bound |
| `enum_schedules.py` | exhaustive enumeration of maximal size-2 schedules (Python) | maximum 48 in the size-2 regime |
| `gen_enum.py` | generalized enumeration with rotations of any size, Python reference implementation | agrees with `gen_enum.c` at small budgets |
| `gen_enum.c` | the C enumerator: every valid schedule node, bottom-completed, rotations of size 2 to 6, budget 30, 512 shards | the exhaustive enumeration, maximum 48 (node count: `../../STATUS.md`) |
| `genrun_logs.tar.gz` | the 512 per-shard logs of the maximal-nodes-only run | |
| `genrun_all_logs.tar.gz` | the 512 per-shard logs of the all-nodes run (same node count, same maximum) | |
| `cube_calibrate.py` | per-cube solve-cost calibration of the schedule CNF over canonical depth-2 cubes; also the reference implementation of the depth-2 canonical set and of rule (b) (`../CAMPAIGN.md`, "Case split") | campaign design only |
| `modal_campaign.py` | a cloud (Modal) driver for the same worker, records and journal; never used for the released journal (`../../docs/history/f6-campaign-FANOUT.md`) | nothing |
| `f6_ge48_fixman0.cnf`, `f6_ge49_fixman0.cnf` | the f(5)-style direct encoding (`../../encode.py`, man 0's list fixed) at order 6 for k = 48 and 49, written before the schedule reduction; never refuted, kept only to document the abandoned route | nothing |

## Rebuilding the enumerator

The compiled binaries are not tracked. From this directory:

    cc -O2 -o gen_enum_c gen_enum.c            # order 6
    cc -O2 -DNVAL=5 -o gen_enum_n5 gen_enum.c  # orders 3, 4, 5 likewise (NVAL=3, 4)
    ./gen_enum_c <budget> <shard> <nshards>    # e.g. budget 30, shards 0..511 of 512

`enum_schedules.py`, `gen_enum.py` and `struct_hunt.py` import
`count_stable` from `hillclimb.py`, so run them from this directory.
`cube_calibrate.py` imports `sched_sat` from `../`.
