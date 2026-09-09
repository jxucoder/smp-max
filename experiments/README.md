# Experiments

These programs record alternative searches and independent computations.
For the primary verification path, start with the [verification guide](../docs/verification.md).
All commands below run from the repository root; new output belongs in `runs/`.

## Enumerators

| Program | Domain |
|---|---|
| [enumerate_cycle_schedules.c](enumeration/enumerate_cycle_schedules.c) | Cycles of all sizes, compiled for n=3–6; configurable budget, sharding, maximal/all-node evaluation, and canonicalization |
| [enumerate_cycle_schedules.py](enumeration/enumerate_cycle_schedules.py) | Independent order-6 general-cycle enumerator with weaker pruning; evaluates all valid nodes |
| [enumerate_full_budget_swaps.py](enumeration/enumerate_full_budget_swaps.py) | Restricted order-6 search: 15 size-2 swaps, full budget |
| [enumerate_f5_profiles.py](enumeration/enumerate_f5_profiles.py) | PySAT enumeration of extremal preference profiles in a selected cube |

Small C sanity run, expected maximum 3 at n=3:

```bash
mkdir -p build
cc -O3 -DNVAL=3 experiments/enumeration/enumerate_cycle_schedules.c -o build/enumerate-cycle-schedules-n3
build/enumerate-cycle-schedules-n3 6 0 1 1 0
```

C arguments are `budget shard nshards evalall nocanon`. `evalall=1`
evaluates every node; the default `0` evaluates maximal nodes. `nocanon=1`
disables canonical pruning. The fixed arrays support the recorded small
orders; this is not an arbitrary-n enumerator.

```bash
python3 -m experiments.enumeration.enumerate_cycle_schedules 6
python3 -m experiments.enumeration.enumerate_full_budget_swaps probe 2
```

The first Python command uses move budget 6, not order 6 as an argument.
For large runs, see the [historical enumeration record](../docs/history/f6-enumeration.md)
and [archived results](../results/f6/enumeration/README.md).

## Searches and earlier SAT experiments

| Program | Purpose |
|---|---|
| [search_instances.py](search/search_instances.py) | Order-6 preference-list hill climbing |
| [search_full_budget_swaps.py](search/search_full_budget_swaps.py) | Order-6 full-budget swap search |
| [search_swap_schedules.py](search/search_swap_schedules.py) | Variable-length size-2 schedule search; accepts n, seed, seconds |
| [search_relaxed_posets.py](search/search_relaxed_posets.py) | Search necessary chain/poset constraints |
| [probe_direct_cubes.py](sat/probe_direct_cubes.py) | Probe earlier Python-encoded order-5 cubes |
| [run_direct_cubes.py](sat/run_direct_cubes.py) | Run those direct cubes; distinct from final Lean selector cubes |

The direct SAT experiments require [requirements-experiments.txt](../requirements-experiments.txt).
Their CLI arguments are documented in the source. The saved order-7 result
can be checked deterministically without repeating a randomized search;
see [f7.md](../docs/f7.md).
