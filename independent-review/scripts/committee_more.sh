#!/usr/bin/env bash
# Optional extra committee Comparator targets (combined acceptance, OPE), same single built tree.
set -u
export PATH=$HOME/.elan/bin:$PATH
export XDG_CACHE_HOME=/path/to/ym-release/review/cache
export LAKE_CACHE_DIR=/path/to/ym-release/review/cache/lake
export MATHLIB_CACHE_DIR=/path/to/ym-release/review/cache/mathlib
export TMPDIR=/path/to/ym-release/review/tmp
SRC=/path/to/ym-release/OpenAI-YM-20261028
LOG=/path/to/ym-release/review/logs
cd /path/to/ym-release/YM/submissions/openai-20261028
for t in acceptance ope; do
  name=26-ym-verify-comparator_target_$t
  start=$(date +%s)
  echo "START $(date -Is) verify.py comparator --target $t --source $SRC" > "$LOG/$name.log"
  python3 -I scripts/verify.py comparator --target $t --source "$SRC" >> "$LOG/$name.log" 2>&1
  rc=$?
  echo "END $(date -Is) EXIT=$rc WALL_SECONDS=$(( $(date +%s) - start ))" >> "$LOG/$name.log"
  echo "$t EXIT=$rc"
done
