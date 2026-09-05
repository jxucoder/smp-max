#!/bin/bash
# Reboot-proof supervisor for this container's campaign driver.
#
# The container can restart at any time (it did at 16:30 UTC on 2026-09-05,
# killing the driver and the checkpoint loop while the disk survived).  This
# script is idempotent: run it from a Routine every hour, or by hand.
#   - if no driver is running, clear the stale lock and scratch and relaunch
#     the exact command line in campaign/driver.cmd (one line, so switching
#     to --shard is an edit of that file);
#   - if no checkpoint loop is running, relaunch snapshot.sh;
#   - print one line per action, nothing when everything is already up.
# IMPORTANT: invoke this script from a run_in_background Bash call (or an
# equivalent detached context).  Observed five times in this container: a
# driver launched from a foreground tool call is killed a few minutes after
# the call returns (4-7 min), whatever nohup/setsid it was given, while one
# launched from a background call runs for hours.
cd /home/user/smp-max/f6 || exit 1
C=campaign
if ! pgrep -f "cube_campaign.py .*--journal $C/campaign.jsonl" >/dev/null; then
  rm -f "$C/campaign.jsonl.lock"; rm -rf "$C"/scratch/w*
  echo "=== RESUME (supervisor) $(date -u) ===" >> "$C/campaign.live.log"
  nohup bash -c "$(cat "$C/driver.cmd")" >> "$C/campaign.live.log" 2>&1 < /dev/null &
  echo "driver relaunched (pid $!): $(cat "$C/driver.cmd")"
fi
if ! pgrep -f "campaign/snapshot.sh" >/dev/null; then
  nohup "$C/snapshot.sh" 3600 > /dev/null 2>&1 < /dev/null &
  echo "checkpoint loop relaunched (pid $!)"
fi
