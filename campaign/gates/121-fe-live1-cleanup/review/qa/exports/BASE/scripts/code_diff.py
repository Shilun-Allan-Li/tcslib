#!/usr/bin/env python3
"""
Review helper: show only the *code* changes between git HEAD and the working tree,
keyed by declaration name rather than by file.

The policy cleanup moved most declarations between files and added ~7000 lines of
docstrings, so `git diff` is dominated by prose and by relocation noise.  This script
strips comments/docstrings, cuts each file into declarations, and compares them by name:

    python3 scripts/code_diff.py --area LearningTheory --stat      # summary table
    python3 scripts/code_diff.py --area CommunicationComplexity    # unified diffs
    python3 scripts/code_diff.py --name deletePath_run_outside_of_some
    python3 scripts/code_diff.py --area LearningTheory --only-new  # just the new lemmas

A declaration that only moved to another file shows up as unchanged (that is the point);
statements are compared too, so a changed signature would appear as a diff.
"""
from __future__ import annotations

import argparse, difflib, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\s+([^\s({\[:]+)")

def strip_comments(text: str) -> str:
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if text.startswith("-/", i) and depth:
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i); i = n if j < 0 else j; continue
        out.append(text[i]); i += 1
    return "".join(out)

def decls(text: str, origin: str) -> dict[str, tuple[str, list[str]]]:
    lines = [l.rstrip() for l in strip_comments(text).split("\n")]
    starts = [i for i, l in enumerate(lines) if DECL.match(l)]
    res: dict[str, tuple[str, list[str]]] = {}
    for k, i in enumerate(starts):
        m = DECL.match(lines[i]); name = m.group(2)
        j = starts[k + 1] if k + 1 < len(starts) else len(lines)
        body = [l for l in lines[i:j] if l.strip()]
        res.setdefault(name, (origin, body))
    return res

def side(area: str, from_head: bool) -> dict[str, tuple[str, list[str]]]:
    res: dict[str, tuple[str, list[str]]] = {}
    if from_head:
        names = subprocess.run(["git", "ls-tree", "-r", "HEAD", "--name-only", f"TCSlib/{area}"],
                               cwd=ROOT, capture_output=True, text=True).stdout.split()
        for n in names:
            if n.endswith(".lean"):
                t = subprocess.run(["git", "show", f"HEAD:{n}"], cwd=ROOT,
                                   capture_output=True, text=True).stdout
                res.update(decls(t, n))
    else:
        for p in sorted((ROOT / "TCSlib" / area).rglob("*.lean")):
            res.update(decls(p.read_text(), str(p.relative_to(ROOT))))
    return res

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--area", action="append", default=[])
    ap.add_argument("--name", default=None, help="show one declaration by name")
    ap.add_argument("--stat", action="store_true")
    ap.add_argument("--only-new", action="store_true")
    a = ap.parse_args()
    areas = a.area or ["LearningTheory", "CommunicationComplexity"]
    tot_ch = tot_new = tot_gone = tot_same = 0
    for area in areas:
        old, new = side(area, True), side(area, False)
        changed = [n for n in old if n in new and old[n][1] != new[n][1]]
        added   = [n for n in new if n not in old]
        gone    = [n for n in old if n not in new]
        same    = len(old) - len(changed) - len(gone)
        tot_ch += len(changed); tot_new += len(added); tot_gone += len(gone); tot_same += same
        print(f"\n=== {area}: {same} unchanged, {len(changed)} changed, "
              f"{len(added)} new, {len(gone)} gone")
        if a.stat:
            for n in sorted(changed):
                o, w = old[n], new[n]
                d = sum(1 for l in difflib.unified_diff(o[1], w[1], n=0) if l[:1] in "+-" and l[:3] not in ("+++", "---"))
                loc = o[0] if o[0] == w[0] else f"{o[0]} → {w[0]}"
                print(f"  {len(o[1]):4d} → {len(w[1]):4d} lines ({d:4d} ±)  {n}   [{loc}]")
            if gone: print("  GONE:", ", ".join(sorted(gone)))
            continue
        if a.only_new:
            for n in sorted(added): print(f"  + {n}   [{new[n][0]}]")
            continue
        for n in sorted(changed):
            if a.name and n != a.name: continue
            o, w = old[n], new[n]
            print(f"\n--- {n}\n--- {o[0]}\n+++ {w[0]}")
            for l in difflib.unified_diff(o[1], w[1], lineterm="", n=2):
                if l[:3] in ("---", "+++"): continue
                print(l)
        if gone: print("\nGONE:", ", ".join(sorted(gone)))
    print(f"\nTOTAL: {tot_same} unchanged, {tot_ch} changed, {tot_new} new, {tot_gone} gone")
    return 0

if __name__ == "__main__":
    sys.exit(main())
