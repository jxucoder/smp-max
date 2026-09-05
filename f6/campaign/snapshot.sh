#!/bin/bash
# Periodic durable checkpoint of the (gitignored) live journal.
# The container is ephemeral; only what is committed survives it.
cd /home/user/smp-max || exit 1
BR=claude/review-state-9u8mt5
while true; do
  sleep "${1:-7200}"
  J=f6/campaign/campaign.jsonl
  [ -f "$J" ] || continue
  V=$(grep -c '"status": "verified"' "$J")
  S=$(grep -c '"status": "split"' "$J")
  T=$(wc -l < "$J")
  gzip -9 -c "$J" > f6/campaign/campaign.jsonl.gz
  git add -A f6/campaign/campaign.jsonl.gz f6/campaign/campaign.log
  git diff --cached --quiet && continue
  git commit -q -m "Campaign journal snapshot: ${V} verified, ${S} splits, ${T} records

Automatic checkpoint from the remote container driving the campaign (the
live campaign.jsonl is gitignored and dies with the container).

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01TNhrpg3rdVzDS9UT39TaUq"
  for i in 2 4 8 16; do
    git push -q -u origin "$BR" && break
    sleep $i
  done
done
