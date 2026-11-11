#!/usr/bin/env bash
# Committee runner stages against the single already-built tree (the OpenAI clone), via --source.
# review/comparator use the default ELAN_HOME (~/.elan, Lean 4.32.0 present); the tools stage
# (run separately) used ELAN_HOME=review/elan-home for the Lean 4.34.0 Comparator toolchain.
set -u
export PATH=$HOME/.elan/bin:$PATH
export XDG_CACHE_HOME=/path/to/ym-release/review/cache
export LAKE_CACHE_DIR=/path/to/ym-release/review/cache/lake
export MATHLIB_CACHE_DIR=/path/to/ym-release/review/cache/mathlib
export TMPDIR=/path/to/ym-release/review/tmp
SRC=/path/to/ym-release/OpenAI-YM-20261028
LOG=/path/to/ym-release/review/logs
cd /path/to/ym-release/YM/submissions/openai-20261028
for stage in "comparator --target submission" "review"; do
  name=24-ym-verify-$(echo $stage | tr ' ' '_' | tr -d '-')
  start=$(date +%s)
  echo "START $(date -Is) verify.py $stage --source $SRC" > "$LOG/$name.log"
  python3 -I scripts/verify.py $stage --source "$SRC" >> "$LOG/$name.log" 2>&1
  rc=$?
  echo "END $(date -Is) EXIT=$rc WALL_SECONDS=$(( $(date +%s) - start ))" >> "$LOG/$name.log"
  echo "$stage EXIT=$rc"
done
