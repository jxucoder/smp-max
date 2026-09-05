#!/bin/bash
# Periodic durable checkpoint of the campaign's live state.
#
# The container is ephemeral and both the journal (campaign.jsonl) and the
# driver's running output (campaign.live.log) are gitignored, so only what
# this script commits survives it.  The tracked campaign.log is regenerated
# at each checkpoint as base + live, which keeps the working tree clean
# between checkpoints instead of dirty on every driver write.
cd /home/user/smp-max || exit 1
BR=claude/review-state-9u8mt5
C=f6/campaign
checkpoint() {
  [ -f "$C/campaign.jsonl" ] || return 0
  V=$(grep -c '"status": "verified"' "$C/campaign.jsonl")
  S=$(grep -c '"status": "split"' "$C/campaign.jsonl")
  T=$(wc -l < "$C/campaign.jsonl")
  cat "$C/campaign.base.log" "$C/campaign.live.log" > "$C/campaign.log"
  gzip -9 -c "$C/campaign.jsonl" > "$C/campaign.jsonl.gz"
  git add -A "$C/campaign.jsonl.gz" "$C/campaign.log"
  git diff --cached --quiet && return 0
  git commit -q -m "Campaign journal snapshot: ${V} verified, ${S} splits, ${T} records

Automatic checkpoint from the remote container driving the campaign.

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01TNhrpg3rdVzDS9UT39TaUq"
  for i in 2 4 8 16; do
    git push -q -u origin "$BR" && return 0
    sleep $i
  done
}
if [ "$1" = "--once" ]; then checkpoint; exit 0; fi
while true; do sleep "${1:-3600}"; checkpoint; done
