#!/usr/bin/env python3
"""Import-graph analysis of the YM project sources.

Usage: python3 -I import_graph.py <repo_root> <out_dir>

Parses `import` lines of every tracked .lean file, computes import closures of
selected roots, and summarizes the Solution closure by top-level YM directory
(modules, lines) and by depth from Solution.
"""
import collections
import json
import os
import re
import subprocess
import sys

root, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
files = subprocess.run(["git", "-C", root, "ls-files", "*.lean"], check=True,
                       capture_output=True, text=True).stdout.split()
mod_of = {f[:-5].replace("/", "."): f for f in files}
imp_re = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»']+)", re.M)

def strip_comments(src):
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)  # imports precede code; nesting irrelevant here
    return re.sub(r"--[^\n]*", "", src)

imports, lines = {}, {}
for m, f in mod_of.items():
    with open(os.path.join(root, f), encoding="utf-8", errors="replace") as fh:
        src = fh.read()
    lines[m] = src.count("\n") + 1
    header = strip_comments(src)
    imports[m] = imp_re.findall(header)

def closure(roots):
    seen, ext, stack = set(), set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen or m in ext:
            continue
        if m not in imports:
            ext.add(m)
            continue
        seen.add(m)
        stack.extend(imports[m])
    return seen, ext

def topdir(m):
    parts = m.split(".")
    return parts[0] + "." + parts[1] if parts[0] == "YM" and len(parts) > 2 else parts[0]

report = {}
for r in ["Challenge", "ChallengeSpec", "Solution", "Construction", "ConcreteSU2", "VerifyJoint", "YM"]:
    s, e = closure([r])
    report[r] = {"project_modules": len(s), "project_lines": sum(lines[m] for m in s),
                 "YM_modules": sum(1 for m in s if m.startswith("YM.")),
                 "external_roots": sorted({x.split(".")[0] for x in e})}
print(json.dumps(report, indent=1))

sol, _ = closure(["Solution"])
allmods = set(imports)
print("tracked modules:", len(allmods), " in Solution closure:", len(sol),
      " not in closure:", len(allmods - sol))
outside = sorted(allmods - sol)
with open(os.path.join(out, "modules_outside_solution_closure.txt"), "w") as fh:
    fh.write("\n".join(outside) + "\n")

# depth from Solution (BFS on import edges)
depth = {"Solution": 0}
q = collections.deque(["Solution"])
while q:
    m = q.popleft()
    for i in imports.get(m, []):
        if i in imports and i not in depth:
            depth[i] = depth[m] + 1
            q.append(i)
by_dir = collections.defaultdict(lambda: [0, 0, 10**9, 0])
for m in sol:
    d = topdir(m)
    by_dir[d][0] += 1
    by_dir[d][1] += lines[m]
    by_dir[d][2] = min(by_dir[d][2], depth[m])
    by_dir[d][3] = max(by_dir[d][3], depth[m])
with open(os.path.join(out, "solution_closure_by_dir.tsv"), "w") as fh:
    fh.write("dir\tmodules\tlines\tmin_depth\tmax_depth\n")
    for d, (n, l, a, b) in sorted(by_dir.items(), key=lambda kv: -kv[1][1]):
        fh.write(f"{d}\t{n}\t{l}\t{a}\t{b}\n")
print("max import depth from Solution:", max(depth.values()))
# reverse-dependency fan-in: which modules are imported by the most closure modules
fanin = collections.Counter()
for m in sol:
    for i in imports[m]:
        if i in sol:
            fanin[i] += 1
with open(os.path.join(out, "fanin_top.txt"), "w") as fh:
    for m, c in fanin.most_common(60):
        fh.write(f"{c}\t{m}\n")
json.dump({m: imports[m] for m in sol}, open(os.path.join(out, "solution_imports.json"), "w"))
json.dump(depth, open(os.path.join(out, "solution_depth.json"), "w"))
json.dump(lines, open(os.path.join(out, "lines.json"), "w"))
