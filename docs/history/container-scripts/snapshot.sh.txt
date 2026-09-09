#!/bin/bash
# Durable checkpoint of this container's campaign state (see supervise.sh).
#
# The journal (campaign.jsonl) and the driver's running output
# (campaign.live.log) are gitignored, so only what this script commits
# survives the container.  The tracked campaign.log is regenerated as
# base + live at each checkpoint, which keeps the working tree clean in
# between.  The journal is gzipped under its own flock (the driver takes
# it per appended line), so a snapshot never contains a torn line.  A
# rejected push is retried after a rebase and reported loudly: a silently
# stranded snapshot would also freeze the seed the shards clone.
#
#     snapshot.sh --once        one checkpoint now
#     snapshot.sh [SECONDS]     loop (default hourly)
cd /home/user/smp-max || exit 1
BR=claude/review-state-9u8mt5
C=f6/campaign
checkpoint() {
  flock -w 900 "$C/checkpoint.lock" bash -c '
    C=$1; BR=$2
    [ -f "$C/campaign.jsonl" ] || exit 0
    cat "$C/campaign.base.log" "$C/campaign.live.log" > "$C/campaign.log"
    flock "$C/campaign.jsonl" gzip -9 -c "$C/campaign.jsonl" > "$C/campaign.jsonl.gz"
    git add -A "$C/campaign.jsonl.gz" "$C/campaign.log"
    git diff --cached --quiet && exit 0
    V=$(grep -c "\"status\": \"verified\"" "$C/campaign.jsonl" || true)
    S=$(grep -c "\"status\": \"split\"" "$C/campaign.jsonl" || true)
    T=$(wc -l < "$C/campaign.jsonl")
    git commit -q -m "Campaign journal snapshot: ${V} verified, ${S} splits, ${T} records

Automatic checkpoint from the remote container driving the campaign.

Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01TNhrpg3rdVzDS9UT39TaUq"
    for w in 2 4 8 16 32; do
      git push -q -u origin "$BR" && exit 0
      git pull -q --rebase origin "$BR" || true
      sleep $w
    done
    echo "snapshot: push to $BR FAILED (journal is on disk)" >&2; exit 1
  ' _ "$C" "$BR"
}
if [ "$1" = "--once" ]; then checkpoint; exit $?; fi
while true; do sleep "${1:-3600}"; checkpoint || true; done
