#!/usr/bin/env bash
# Post-build verification steps, run sequentially with timing.
# 1-3: the README's three `lake env lean` commands (Usage.lean is run from a scratch cwd
#      because it writes verification/*.tsv relative to the cwd; this keeps tracked files intact).
# 4-5: this review's own audit files (outside the clone).
set -u
source /path/to/ym-release/review/env.sh
REPO=/path/to/ym-release/OpenAI-YM-20261028
LOG=/path/to/ym-release/review/logs
step () {  # name cwd cmd...
  local name=$1 cwd=$2; shift 2
  local start=$(date +%s)
  echo "START $(date -Is) cwd=$cwd cmd=$*" > "$LOG/$name.log"
  ( cd "$cwd" && /usr/bin/time -f "TIME wall=%e s maxrss=%M KB" "$@" ) >> "$LOG/$name.log" 2>&1
  local rc=$?
  echo "END $(date -Is) EXIT=$rc WALL_SECONDS=$(( $(date +%s) - start ))" >> "$LOG/$name.log"
  echo "$name EXIT=$rc"
}
step 03-verify-joint "$REPO" lake env lean -j1 -DmaxHeartbeats=0 -DmaxRecDepth=4096 VerifyJoint.lean
mkdir -p /path/to/ym-release/review/run-usage/verification
cp "$REPO/verification/joint-headlines.txt" /path/to/ym-release/review/run-usage/verification/
step 04-usage /path/to/ym-release/review/run-usage lake -d "$REPO" env lean -j1 -DmaxHeartbeats=0 "$REPO/verification/Usage.lean"
step 05-compact-check "$REPO" lake env lean -j1 verification/CompactCheck.lean
step 31-own-audit "$REPO" lake env lean -DmaxHeartbeats=0 /path/to/ym-release/review/lean/OwnAudit.lean
step 32-arch-map "$REPO" lake env lean -DmaxHeartbeats=0 /path/to/ym-release/review/lean/ArchMap.lean
step 33-own-replay "$REPO" lake env lean -DmaxHeartbeats=0 /path/to/ym-release/review/lean/OwnReplay.lean
echo "POST_BUILD_DONE $(date -Is)"
