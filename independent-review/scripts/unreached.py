#!/usr/bin/env python3
"""Summarize reached / unreached project declarations from review/work/audit/declarations.tsv.

Usage: python3 -I unreached.py <declarations.tsv>
Columns: declaration module topdir kind internal reached_from_jointExistence reached_from_17
"""
import collections
import csv
import sys

rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
T = lambda r, k: r[k] == "true"
tot = len(rows)
r1 = sum(T(r, "reached_from_jointExistence") for r in rows)
r17 = sum(T(r, "reached_from_17") for r in rows)
print(f"project declarations: {tot}; reached from jointExistence: {r1}; reached from 17 endpoints: {r17}; unreached (17): {tot - r17}")
gen = lambda r: r["internal"] == "true" or any(s in r["declaration"] for s in
    ("._", ".match_", ".proof_", ".eq_", "._sunfold", ".induct", ".brecOn", ".below", ".rec", ".casesOn",
     ".noConfusion", ".mk.inj", ".sizeOf_spec", ".ext_iff", ".injEq", ".recOn", "._simp_", ".congr_simp"))
src = [r for r in rows if not gen(r)]
print(f"source-level (heuristic: not internal/auxiliary): {len(src)}; reached(17): {sum(T(r,'reached_from_17') for r in src)}; "
      f"unreached(17): {sum(not T(r,'reached_from_17') for r in src)}")
by_kind = collections.Counter((r["kind"], T(r, "reached_from_17")) for r in rows)
print("by kind (kind, reached17): count")
for k, v in sorted(by_kind.items()):
    print(f"  {k}: {v}")
mods = collections.defaultdict(lambda: [0, 0])
for r in rows:
    m = mods[r["module"]]
    m[0] += 1
    m[1] += T(r, "reached_from_17")
zero = [m for m, (a, b) in mods.items() if b == 0]
print(f"modules with project declarations: {len(mods)}; modules with no reached declaration: {len(zero)}")
dirz = collections.Counter(r["topdir"] for r in rows if not T(r, "reached_from_17"))
dirt = collections.Counter(r["topdir"] for r in rows)
print("unreached(17) by top-level dir (top 25): dir unreached/total (share)")
for d, c in dirz.most_common(25):
    print(f"  {d}: {c}/{dirt[d]} ({100*c/dirt[d]:.0f}%)")
zd = collections.Counter(".".join(m.split(".")[:3]) for m in zero)
print("modules with zero reached declarations, grouped by YM.<dir>.<subdir> (top 25):")
for d, c in zd.most_common(25):
    print(f"  {d}: {c}")
