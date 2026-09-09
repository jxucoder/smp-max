# Earlier schedule enumeration

The [maximal-node archive](maximal-node-logs.tar.gz) contains `genrun/s0.log`
through `genrun/s511.log`. The [all-node archive](all-node-logs.tar.gz)
contains `genrun_all/s0.log` through `genrun_all/s511.log`. Both original
archives are unchanged. Their 1,024 corresponding loose log files were
byte-compared before deduplication; archive metadata entries were retained.

Inspect a shard from the repository root:

```bash
tar -xOf results/f6/enumeration/all-node-logs.tar.gz genrun_all/s0.log
```

The historical all-node run evaluated 26,574,282,886 schedule nodes with
maximum 48. The source is now [enumerate_cycle_schedules.c](../../../experiments/enumeration/enumerate_cycle_schedules.c);
build and flag instructions are in [experiments/README.md](../../../experiments/README.md).

The `bin-macos-arm64/` directory preserves four historical executable bytes
for provenance. `gen_enum_c` is the order-6 binary; `gen_enum_n3`,
`gen_enum_n4`, and `gen_enum_n5` are the smaller-order builds. Their names
and hashes are retained. Normal use should build the source for the host
platform into ignored `build/`, rather than assuming these binaries are portable.
