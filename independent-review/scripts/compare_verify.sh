#!/usr/bin/env bash
# Compare this review's reruns of the README verification commands with the shipped logs.
set -u
R=/path/to/ym-release/OpenAI-YM-20261028/verification
L=/path/to/ym-release/review/logs
W=/path/to/ym-release/review/work/compare
mkdir -p "$W"
pat='^(TYPE_MATCH|ENDPOINT_AXIOMS|REPLAY_START|REPLAY_PASS|Entering kernel replay)'
grep -E "$pat" "$R/joint-check.log" > "$W/shipped-joint.txt"
grep -E "$pat" "$L/03-verify-joint.log" > "$W/ours-joint.txt"
echo "== VerifyJoint lines: shipped $(wc -l < $W/shipped-joint.txt), ours $(wc -l < $W/ours-joint.txt)"
diff <(sort "$W/shipped-joint.txt") <(sort "$W/ours-joint.txt") && echo "VERIFYJOINT_LINES_IDENTICAL (as sets)"
echo "== CompactCheck"
grep -E 'COMPACT' "$L/05-compact-check.log" > "$W/ours-compact.txt"
diff "$R/compact-check.log" "$W/ours-compact.txt" && echo "COMPACT_LINES_IDENTICAL"
echo "== Usage summary line"
grep -o 'USAGE_PASS.*' "$L/04b-usage.log"
cat "$R/usage.log"
echo "== Usage TSVs (regenerated in review/run-usage/verification) vs shipped"
for f in declaration-usage.tsv module-usage.tsv; do
  a="$R/$f"; b=/path/to/ym-release/review/run-usage/verification/$f
  if [ -f "$b" ]; then
    echo "$f: shipped $(wc -l < $a) lines sha=$(sha256sum < $a | cut -c1-12); ours $(wc -l < $b) lines sha=$(sha256sum < $b | cut -c1-12)"
    diff <(sort "$a") <(sort "$b") > "$W/diff-$f.txt"; echo "  differing lines (sorted diff): $(grep -c '^[<>]' $W/diff-$f.txt)"
    head -8 "$W/diff-$f.txt"
  else echo "$f: not regenerated"; fi
done
