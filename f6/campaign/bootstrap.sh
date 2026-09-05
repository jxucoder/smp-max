#!/bin/bash
# Bring a fresh Linux/x86-64 container from a bare checkout to a running
# campaign shard, idempotently:
#
#     f6/campaign/bootstrap.sh I N [WORKERS] [BRANCH]
#
# 1. builds CaDiCaL at the journal header's pinned commit and cake_lpr from
#    its verified assembly (hash-checked), self-tests both;
# 2. seeds the shard journal from the committed snapshot campaign.jsonl.gz
#    (so it skips every cube already certified) unless one exists already;
# 3. starts an hourly checkpoint loop that gzips the shard journal and
#    pushes it with the run log to BRANCH (default claude/campaign-shard-I-of-N);
# 4. runs cube_campaign.py --shard I/N in the foreground (rerun the same
#    command to resume after any interruption).
set -euo pipefail
I=${1:?usage: bootstrap.sh I N [WORKERS] [BRANCH]}; N=${2:?}
WORKERS=${3:-3}
BRANCH=${4:-claude/campaign-shard-$I-of-$N}
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
CADICAL_COMMIT=c60730422e758ef1cebe7aeddf2dda31c996bf04
CAKE_S_SHA=2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a

cd "$ROOT"
if [ ! -x cadical-src/build/cadical ]; then
  [ -d cadical-src ] || git clone -q https://github.com/arminbiere/cadical.git cadical-src
  (cd cadical-src && git checkout -q $CADICAL_COMMIT && ./configure >/dev/null && make -j"$(nproc)" >/dev/null)
fi
cadical-src/build/cadical --build | head -1 | grep -q "$CADICAL_COMMIT"
if [ ! -x cake_lpr-src/cake_lpr ]; then
  [ -d cake_lpr-src ] || git clone -q https://github.com/tanyongkiam/cake_lpr.git cake_lpr-src
  (cd cake_lpr-src && echo "$CAKE_S_SHA  cake_lpr.S" | sha256sum -c - >/dev/null && make cake_lpr >/dev/null 2>&1)
fi
cake_lpr-src/cake_lpr cake_lpr-src/example.cnf cake_lpr-src/example.lpr | grep -q "s VERIFIED UNSAT"
echo "toolchain ok: $(cadical-src/build/cadical --build | head -1); cake_lpr self-test passed"

C=f6/campaign; S=$C/shards; mkdir -p "$S"
J=$S/shard_${I}_of_${N}.jsonl
LOG=$S/shard_${I}_of_${N}.log
[ -s "$J" ] || gunzip -c "$C/campaign.jsonl.gz" > "$J"
echo "journal $J: $(wc -l < "$J") records"

# a commit needs an identity; a fresh container may have none configured
git config user.name  >/dev/null || git config user.name  "campaign shard $I/$N"
git config user.email >/dev/null || git config user.email "shard-$I-of-$N@campaign.invalid"

# checkpoint: only what is pushed survives the container.  Exits non-zero
# when nothing could be pushed so a failure is visible in the log.
checkpoint() {
  gzip -9 -c "$J" > "$J.gz"
  git add -A "$J.gz" "$LOG"
  git diff --cached --quiet && return 0
  V=$(grep -c '"status": "verified"' "$J" || true); SP=$(grep -c '"status": "split"' "$J" || true)
  git commit -q -m "Shard $I/$N snapshot: $V verified, $SP splits, $(wc -l < "$J") records"
  for w in 2 4 8 16 32; do git push -q -u origin HEAD:"$BRANCH" && return 0; sleep $w; done
  echo "checkpoint: push to $BRANCH failed" >&2; return 1
}
( while true; do sleep 3600; checkpoint || true; done ) &
LOOP=$!
echo "checkpoint loop pid $LOOP -> $BRANCH"

echo "=== shard $I/$N start $(date -u) ===" >> "$LOG"
set +e
python3 f6/cube_campaign.py --solver cadical --shard "$I/$N" --workers "$WORKERS" \
  --time 300 --max-depth 4 --shuffle --journal "$J" --scratch "$C/scratch_shard_$I" >> "$LOG" 2>&1
RC=$?
set -e
kill "$LOOP" 2>/dev/null || true
checkpoint            # final snapshot the moment the driver stops, whatever the reason
echo "driver exited rc=$RC; final checkpoint pushed to $BRANCH"
exit $RC
