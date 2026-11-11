#!/usr/bin/env python3
"""Print the leading module docstring (first ~220 chars) of files in a YM subdirectory.

Usage: python3 -I dir_docs.py <repo_root> <YM/Subdir> [max_files]
"""
import os
import re
import subprocess
import sys

root, sub = sys.argv[1], sys.argv[2]
mx = int(sys.argv[3]) if len(sys.argv) > 3 else 25
files = subprocess.run(["git", "-C", root, "ls-files", f"{sub}/*.lean", f"{sub}/**/*.lean"],
                       check=True, capture_output=True, text=True).stdout.split()
files = sorted(set(files))
doc_re = re.compile(r"/-[!-](.*?)-/", re.S)
shown = 0
for f in files:
    with open(os.path.join(root, f), encoding="utf-8", errors="replace") as fh:
        src = fh.read()
    m = doc_re.search(src)
    if not m:
        continue
    text = " ".join(m.group(1).split())
    print(f"{f}: {text[:220]}")
    shown += 1
    if shown >= mx:
        break
print(f"[{shown} of {len(files)} files shown]")
