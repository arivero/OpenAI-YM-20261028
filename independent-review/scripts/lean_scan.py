#!/usr/bin/env python3
"""Comment/string-aware token scan of Lean 4 sources.

Usage: python3 -I lean_scan.py <repo_root> <out_dir>

Strips nested block comments (/- ... -/, including doc comments) and line
comments (-- ...), blanks string literals, then searches the remaining code
for escape-hatch tokens.  Writes per-pattern hit files and prints counts.
Raw (comment-inclusive) counts are reported as well, for comparison.
"""
import os
import re
import subprocess
import sys

root, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
files = subprocess.run(["git", "-C", root, "ls-files", "*.lean"], check=True,
                       capture_output=True, text=True).stdout.split()


def strip(src: str) -> str:
    """Replace comments and string contents by spaces, preserving newlines."""
    res = []
    i, n, depth = 0, len(src), 0
    in_str = False
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1; res.append("  "); i += 2; continue
            if c == "-" and nxt == "/":
                depth -= 1; res.append("  "); i += 2; continue
            res.append("\n" if c == "\n" else " "); i += 1; continue
        if in_str:
            if c == "\\" and i + 1 < n:
                res.append("  " if nxt != "\n" else " \n"); i += 2; continue
            if c == '"':
                in_str = False; res.append('"'); i += 1; continue
            res.append("\n" if c == "\n" else " "); i += 1; continue
        if c == "/" and nxt == "-":
            depth = 1; res.append("  "); i += 2; continue
        if c == "-" and nxt == "-":
            j = src.find("\n", i)
            j = n if j < 0 else j
            res.append(" " * (j - i)); i = j; continue
        if c == '"':
            # crude char-literal guard: '"' as a Char literal
            if i > 0 and src[i - 1] == "'" and i + 1 < n and src[i + 1] == "'":
                res.append(c); i += 1; continue
            in_str = True; res.append('"'); i += 1; continue
        res.append(c); i += 1
    return "".join(res)


B = r"(?<![\w.'!?])"   # left identifier boundary
E = r"(?![\w'!?])"     # right identifier boundary
patterns = {
    "sorry": B + r"sorry" + E,
    "sorryAx": r"sorryAx",
    "admit": B + r"admit" + E,
    "axiom_decl": r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*axiom\s",
    "axiom_token": B + r"axiom" + E,
    "native_decide": B + r"native_decide" + E,
    "decide_native_option": r"decide\s*\+\s*native|native\s*:=\s*true|kernel\s*:=\s*false",
    "ofReduceBool": r"ofReduceBool|ofReduceNat",
    "trustCompiler": r"trustCompiler",
    "unsafe": B + r"unsafe" + E,
    "implemented_by": B + r"implemented_by" + E,
    "extern": B + r"extern" + E,
    "opaque": B + r"opaque" + E,
    "partial": B + r"partial" + E,
    "set_option_debug": r"set_option\s+debug\.",
    "set_option_any": r"set_option\s+[\w.]+",
    "elab_kw": r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|local|scoped)\s+)*(?:elab|elab_rules|term_elab|command_elab|tactic_elab)" + E,
    "macro_kw": r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|local|scoped)\s+)*(?:macro|macro_rules)" + E,
    "syntax_kw": r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|local|scoped)\s+)*(?:syntax|declare_syntax_cat)" + E,
    "notation_kw": r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|local|scoped)\s+)*(?:notation|infix|infixl|infixr|prefix|postfix|notation3)" + E,
    "initialize": B + r"(?:initialize|builtin_initialize)" + E,
    "run_cmd_eval": r"(?m)^\s*(?:run_cmd|run_elab|run_meta|#eval|#eval!)" + E,
    "import_Lean_meta": r"(?m)^\s*import\s+(?:Lean|Lean\.\S*|Qq|Aesop|Batteries\.Lean\S*|Mathlib\.Tactic\S*|Mathlib\.Lean\S*)\s*$",
    "env_hack": r"modifyEnv|addDecl|addAndCompile|Environment\.|setEnv|Kernel\.|replay|ofExcept|evalConst|unsafeCast|unsafeBaseIO|unsafeIO|ptrEq|withUnsafe",
    "attribute_cmd": r"(?m)^\s*attribute\s*\[",
    "register_attr": r"register_\w+attr|registerBuiltinAttribute|register_simp_attr|register_option|register_label_attr",
    "instance_priority": r"instance\s*\(priority",
    "csimp_inline": r"@\[\s*(?:csimp|implemented_by|extern|export)",
    "redefine_std": r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|structure|class|inductive|opaque|axiom)\s+(?:_root_\.)?(?:Real|Complex|Nat|Int|MeasureTheory\.\w+|Continuous|Measurable|SchwartzMap|EuclideanSpace|Matrix|Filter\.Tendsto|Tendsto|IsProbabilityMeasure|Measure|HilbertSpace|InnerProductSpace|ContDiff|ContDiffOn|DifferentiableOn|Real\.\w+|Complex\.\w+)" + E,
    "namespace_std": r"(?m)^\s*namespace\s+(?:_root_\.)?(?:Real|Complex|MeasureTheory|Filter|Matrix|SchwartzMap|Nat|Int|ContinuousLinearMap|Submodule|Finset|Function|Set|Lean)" + E,
    "root_decl": r"_root_\.",
    "theorem_keyword_override": r"(?m)^\s*(?:syntax|macro|elab)[^\n]*\"(?:theorem|lemma|def|example|instance)\"",
}

counts = {}
raw_counts = {}
hits = {k: [] for k in patterns}
regex = {k: re.compile(v) for k, v in patterns.items()}
for f in files:
    path = os.path.join(root, f)
    with open(path, encoding="utf-8", errors="replace") as fh:
        src = fh.read()
    code = strip(src)
    lines = src.split("\n")
    for k, rx in regex.items():
        for m in rx.finditer(src):
            raw_counts[k] = raw_counts.get(k, 0) + 1
        for m in rx.finditer(code):
            st = m.start()
            while st < m.end() and code[st] in " \t\n":
                st += 1
            ln = code.count("\n", 0, st) + 1
            hits[k].append(f"{f}:{ln}: {lines[ln - 1].strip()[:200]}")
for k in patterns:
    counts[k] = len(hits[k])
    with open(os.path.join(out, f"{k}.txt"), "w") as fh:
        fh.write("\n".join(hits[k]) + ("\n" if hits[k] else ""))
print(f"files scanned: {len(files)}")
print(f"{'pattern':28s} {'code-hits':>10s} {'raw-hits(incl. comments)':>26s}")
for k in patterns:
    print(f"{k:28s} {counts[k]:10d} {raw_counts.get(k, 0):26d}")
