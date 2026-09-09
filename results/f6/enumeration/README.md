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

Historical macOS binaries were removed upstream and remain in Git history
at `30ad2c3`. Build the source for the host platform into ignored `build/`.
