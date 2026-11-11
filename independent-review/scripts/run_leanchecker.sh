#!/usr/bin/env bash
# Kernel replay of every project module with the toolchain's own `leanchecker`
# (upstreamed lean4checker, shipped in Lean v4.32.0). For each module it replays the
# module's declarations into the environment of its imports and runs the kernel.
# Usage: run_leanchecker.sh <threads> <module-prefix>...
set -u
source /path/to/ym-release/review/env.sh
threads=$1; shift
cd /path/to/ym-release/OpenAI-YM-20261028
LOG=/path/to/ym-release/review/logs/40-leanchecker.log
start=$(date +%s)
echo "START $(date -Is) threads=$threads targets=$*" > "$LOG"
LEAN_NUM_THREADS=$threads /usr/bin/time -v lake env /path/to/home/.elan/toolchains/leanprover--lean4---v4.32.0/bin/leanchecker -v "$@" >> "$LOG" 2>&1
rc=$?
echo "END $(date -Is) EXIT=$rc WALL_SECONDS=$(( $(date +%s) - start ))" >> "$LOG"
exit $rc
