# Fan-out record (2026-09-05 18:41 UTC)

Campaign split into 8 shards from seed snapshot `0a1d6c3` (13,410
verified, 687 splits, 14,164 records), branch `claude/review-state-9u8mt5`
at `f2f72a8`.

| shard | where | branch | session |
|---|---|---|---|
| 0/8 | this container (`driver.cmd`, hourly `supervise.sh` Routine `trig_018DLAZ7PPKv9VbVGNw2bmC2`) | `claude/review-state-9u8mt5` (journal `campaign/campaign.jsonl.gz`) | `session_01TNhrpg3rdVzDS9UT39TaUq` |
| 1/8 | cloud | `claude/campaign-shard-1-of-8` | `session_019Ci2QmAeBKe9acjPZQUwsB` |
| 2/8 | cloud | `claude/campaign-shard-2-of-8` | `session_0178NaRWYvE1zyTBqrniNFE7` |
| 3/8 | cloud | `claude/campaign-shard-3-of-8` | `session_01E58AqGfQvZ6JihxGBhsozF` |
| 4/8 | cloud | `claude/campaign-shard-4-of-8` | `session_01JFGsFArvhDp94NvneNgeJ8` |
| 5/8 | cloud | `claude/campaign-shard-5-of-8` | `session_019dPtRDgZZnKawcfyj9wy7j` |
| 6/8 | cloud | `claude/campaign-shard-6-of-8` | `session_01E6HCRMdoHWjwSrY6hw15od` |
| 7/8 | cloud | `claude/campaign-shard-7-of-8` | `session_01K7XYJs3mfBramL1t8Dfifb` |

Each cloud shard runs `f6/campaign/bootstrap.sh I 8 3` (3 workers) and
an hourly Routine bound to its own session that re-runs it (checkpoint
only while the driver is up; resume after a container reboot). Its
journal is `f6/campaign/shards/shard_I_of_8.jsonl.gz` on its branch.

## Progress

    git fetch origin 'refs/heads/claude/campaign-shard-*:refs/remotes/origin/claude/campaign-shard-*'
    for b in $(git branch -r | grep campaign-shard); do echo "$b: $(git log -1 --format=%s $b)"; done

## Merge and audit (when every shard's log ends with `done:` and its last `to run:` is 0)

    mkdir -p f6/campaign/merge && cd f6/campaign/merge
    for i in 1 2 3 4 5 6 7; do
      git show origin/claude/campaign-shard-$i-of-8:f6/campaign/shards/shard_${i}_of_8.jsonl.gz > shard_${i}_of_8.jsonl.gz
    done
    cd ../../.. && python3 f6/merge_journals.py -o f6/campaign/merge/merged.jsonl \
        f6/campaign/campaign.jsonl f6/campaign/merge/shard_*_of_8.jsonl.gz
    python3 f6/cube_campaign.py --audit --journal f6/campaign/merge/merged.jsonl   # exit 0 iff complete

Any `bad`/`missing` in the audit names the cubes to re-run (`--cubes ... --force`
on any journal, then merge again).

## Outcome (2026-09-06 03:00 UTC): cloud fan-out retired, handoff to the laptop

The seven cloud shards never got past their preflight push: an
Anthropic-hosted container is reclaimed minutes after its session goes
idle (uptime resets, processes die, disk survives), so a shard session
that finished its setup turn lost its driver. Their Routines are
disabled and the sessions archived; the `claude/campaign-shard-*-of-8`
branches carry nothing beyond the seed commit and can be deleted. This
container kept certifying under a keep-alive Monitor (no reboot for the
last 7.5 h); its journal is the snapshot in this commit and is the
resume point.

Resume on the laptop (same journal, same driver):

    gunzip -c f6/campaign/campaign.jsonl.gz > f6/campaign/campaign.jsonl
    cd f6 && python3 cube_campaign.py --solver cadical --workers 10 --time 300 \
        --max-depth 4 --shuffle --retry-status error,cake_fail,check_timeout \
        --journal campaign/campaign.jsonl --scratch campaign/scratch

or hand the remaining ~130k cubes to Modal from the laptop (the client
needs no proxy there): `pip install modal && modal token new && modal run
f6/modal_campaign.py --sample 50`, then without `--sample`; it appends to
the same journal. Either way `cube_campaign.py --audit` is the finish line.
