#!/bin/bash
# Bring a Linux/x86-64 container from a bare checkout to a running campaign
# shard, idempotently.  Safe to re-run at any time (e.g. hourly from a
# Routine): if this shard's driver is already running it takes one
# checkpoint and exits 0; after a container restart it resumes.
#
#     f6/campaign/tools/bootstrap.sh I N [WORKERS] [BRANCH]
#
# 1. builds CaDiCaL at the journal header's pinned commit and cake_lpr from
#    its hash-checked verified assembly, self-tests both;
# 2. resumes from origin's shard branch if it exists (a replaced container
#    must never re-seed from the base snapshot and then push non-fast-
#    forward), else creates the branch from the current checkout; seeds the
#    shard journal, in this order of preference, from the live journal, the
#    branch's last checkpoint shard_I_of_N.jsonl.gz, or the committed base
#    snapshot campaign.jsonl.gz - complete JSON lines only;
# 3. pushes the branch once BEFORE starting, so a container that cannot
#    push aborts instead of working for hours into the void;
# 4. runs the driver with an hourly checkpoint (journal gzipped under the
#    journal's own lock, so never a torn line; commit; push with a rebase
#    retry), a checkpoint on exit, and a trap so SIGTERM/SIGINT/SIGHUP stop
#    the driver and checkpoint too.
set -euo pipefail
I=${1:?usage: bootstrap.sh I N [WORKERS] [BRANCH]}; N=${2:?}
WORKERS=${3:-3}
BRANCH=${4:-claude/campaign-shard-$I-of-$N}
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)   # tools/ -> campaign/ -> f6/ -> repo root
CADICAL_COMMIT=c60730422e758ef1cebe7aeddf2dda31c996bf04
CAKE_S_SHA=2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a
cd "$ROOT"
C=f6/campaign; S=$C/shards
J=$S/shard_${I}_of_${N}.jsonl
LOG=$S/shard_${I}_of_${N}.log

checkpoint() {
  # serialized against itself; the gzip holds the journal's flock, which the
  # driver takes per appended line, so the snapshot has no torn line
  flock -w 900 "$C/checkpoint.lock" bash -c '
    set -u; J=$1; LOG=$2; BRANCH=$3; I=$4; N=$5
    flock "$J" gzip -9 -c "$J" > "$J.gz"
    git add -A "$J.gz" "$LOG"
    git diff --cached --quiet && exit 0
    V=$(grep -c "\"status\": \"verified\"" "$J" || true)
    SP=$(grep -c "\"status\": \"split\"" "$J" || true)
    git commit -q -m "Shard $I/$N snapshot: $V verified, $SP splits, $(wc -l < "$J") records"
    for w in 2 4 8 16 32; do
      git push -q origin "$BRANCH" && exit 0
      git pull -q --rebase origin "$BRANCH" || true
      sleep $w
    done
    echo "checkpoint: push to $BRANCH FAILED" >&2; exit 1
  ' _ "$J" "$LOG" "$BRANCH" "$I" "$N"
}

# --- already running?  (the driver holds an exclusive flock on <journal>.lock)
if [ -e "$J.lock" ] && ! flock -n "$J.lock" true; then
  echo "shard $I/$N driver already running; checkpoint only"
  checkpoint; exit 0
fi

# --- toolchain
if [ ! -x cadical-src/build/cadical ]; then
  [ -d cadical-src ] || git clone -q https://github.com/arminbiere/cadical.git cadical-src
  (cd cadical-src && git checkout -q $CADICAL_COMMIT && ./configure >/dev/null && make -j"$(nproc)" >/dev/null)
fi
cadical-src/build/cadical --build | head -1 | grep -q "$CADICAL_COMMIT" \
  || { echo "cadical-src/build/cadical is not commit $CADICAL_COMMIT; remove cadical-src and rerun"; exit 1; }
if [ ! -x cake_lpr-src/cake_lpr ]; then
  [ -d cake_lpr-src ] || git clone -q https://github.com/tanyongkiam/cake_lpr.git cake_lpr-src
  (cd cake_lpr-src && echo "$CAKE_S_SHA  cake_lpr.S" | sha256sum -c - >/dev/null && make cake_lpr >/dev/null 2>&1)
fi
cake_lpr-src/cake_lpr cake_lpr-src/example.cnf cake_lpr-src/example.lpr | grep -q "s VERIFIED UNSAT"
echo "toolchain ok: $(cadical-src/build/cadical --build | head -1); cake_lpr self-test passed"

# --- git identity, branch, seed, push preflight
git config user.name  >/dev/null || git config user.name  "campaign shard $I/$N"
git config user.email >/dev/null || git config user.email "shard-$I-of-$N@campaign.invalid"
if git fetch -q origin "$BRANCH" 2>/dev/null; then
  if git show-ref -q --verify "refs/heads/$BRANCH"; then
    git checkout -q "$BRANCH"
    git merge -q --ff-only "origin/$BRANCH" || echo "local $BRANCH is ahead of origin; keeping local commits"
  else
    git checkout -q -b "$BRANCH" "origin/$BRANCH"
  fi
  echo "resuming shard branch origin/$BRANCH ($(git rev-parse --short HEAD))"
else
  git checkout -q -B "$BRANCH"
  echo "new shard branch $BRANCH from $(git rev-parse --short HEAD)"
fi
mkdir -p "$S"
if [ ! -s "$J" ]; then
  SRC=$C/campaign.jsonl.gz; [ -s "$J.gz" ] && SRC=$J.gz
  gunzip -c "$SRC" | python3 -c '
import sys, json
for line in sys.stdin:
    try:
        json.loads(line)
    except ValueError:
        continue
    sys.stdout.write(line if line.endswith("\n") else line + "\n")' > "$J"
  echo "seeded $J from $SRC: $(wc -l < "$J") complete records"
else
  echo "journal $J: $(wc -l < "$J") records (kept)"
fi
git push -q -u origin "$BRANCH" || { echo "cannot push to origin/$BRANCH; aborting before any work"; exit 1; }

# --- run
set +e
( while true; do sleep 3600; checkpoint || true; done ) &
LOOP=$!
echo "=== shard $I/$N start $(date -u) ===" >> "$LOG"
python3 f6/cube_campaign.py --solver cadical --shard "$I/$N" --workers "$WORKERS" \
  --time 300 --max-depth 4 --shuffle --retry-status error,cake_fail,check_timeout \
  --journal "$J" --scratch "$C/scratch_shard_$I" >> "$LOG" 2>&1 &
DRV=$!
finish() {
  trap - TERM INT HUP
  kill "$LOOP" 2>/dev/null
  if kill -0 "$DRV" 2>/dev/null; then kill -TERM "$DRV" 2>/dev/null; wait "$DRV" 2>/dev/null; fi
  checkpoint && echo "final checkpoint pushed to $BRANCH" || echo "final checkpoint FAILED (journal is on disk: $J)"
}
trap 'finish; exit 143' TERM INT HUP
echo "shard $I/$N driver pid $DRV, checkpoint loop $LOOP -> $BRANCH"
wait "$DRV"; RC=$?
finish
echo "driver exited rc=$RC"
exit $RC
