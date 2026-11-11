#!/usr/bin/env bash
# Runs the README build step with timing, plus a memory sampler that exits with the build.
# Usage: run_build.sh <logname> <lake args...>
set -u
source /path/to/ym-release/review/env.sh
LOGDIR=/path/to/ym-release/review/logs
name=$1; shift
cd /path/to/ym-release/OpenAI-YM-20261028
(
  while true; do
    printf '%s ' "$(date +%H:%M:%S)"
    free -m | awk '/Mem:/{printf "used=%dM avail=%dM ",$3,$7} /Swap:/{printf "swap_used=%dM ",$3}'
    ps -C lean -o rss= 2>/dev/null | awk '{n++; s+=$1; if($1>m)m=$1} END{printf "lean_procs=%d lean_rss_sum=%dM lean_rss_max=%dM\n",n,s/1024,m/1024}'
    sleep 60
  done
) > "$LOGDIR/$name.mem.log" 2>&1 &
sampler=$!
start=$(date +%s)
echo "START $(date -Is) lake $*" > "$LOGDIR/$name.log"
/usr/bin/time -v lake "$@" >> "$LOGDIR/$name.log" 2>&1
rc=$?
end=$(date +%s)
kill $sampler 2>/dev/null
echo "END $(date -Is) EXIT=$rc WALL_SECONDS=$((end-start))" >> "$LOGDIR/$name.log"
exit $rc
