"""Freeze check for Diagonal Part 1 (read-only; standard library only).

Usage: python3 -I freeze.py <base Diagonal.lean> <landed Diagonal.lean>

For every declaration of the base file: it must exist in the landed file with the same kind and
fully qualified name, and its head (from the keyword up to, not including, the top-level ` :=`
or ` where`) must be byte-identical. Reports which bodies and docstrings changed, the new
declarations, the header (copyright, imports, options) comparison, and `sorry`/`admit`
occurrences in code (comments stripped). Exit 1 on any failure.
"""
import re
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from decls import parse  # noqa: E402


def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            i += 1
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def header(src):
    """Everything before the module docstring `/-!`."""
    return src[:src.index("/-!")]


def main():
    base_src = open(sys.argv[1], encoding="utf-8").read()
    land_src = open(sys.argv[2], encoding="utf-8").read()
    base, land = parse(base_src), parse(land_src)
    lmap = {(d["kind"], d["name"]): d for d in land}
    fail = []
    print("## Header (copyright block, imports, options: everything before the module docstring)")
    same_header = header(base_src) == header(land_src)
    print(f"byte-identical: {same_header}")
    if not same_header:
        fail.append("header changed")
    print()
    print(f"## Received declarations ({len(base)}): heads byte-identical, bodies, docstrings")
    print("| declaration | kind | visibility | head | body | docstring |")
    print("|---|---|---|---|---|---|")
    for d in base:
        e = lmap.get((d["kind"], d["name"]))
        if e is None:
            fail.append(f"missing: {d['name']}")
            print(f"| `{d['name']}` | {d['kind']} | | **MISSING** | | |")
            continue
        h = "identical" if e["head"] == d["head"] else "**CHANGED**"
        if e["head"] != d["head"]:
            fail.append(f"head changed: {d['name']}")
        if e["private"] != d["private"]:
            fail.append(f"visibility changed: {d['name']}")
        b = "unchanged" if e["body"] == d["body"] else "changed"
        dc = "unchanged" if e["doc"] == d["doc"] else "changed"
        vis = "private" if d["private"] else "public"
        print(f"| `{d['name']}` | {d['kind']} | {vis} | {h} | {b} | {dc} |")
    print()
    bnames = {(d["kind"], d["name"]) for d in base}
    new = [d for d in land if (d["kind"], d["name"]) not in bnames]
    print(f"## New declarations ({len(new)})")
    for d in new:
        vis = "private" if d["private"] else "public"
        print(f"- `{d['name']}` ({d['kind']}, {vis}, line {d['line']}; docstring: "
              f"{'yes' if d['doc'] else 'NO'})")
        if not d["doc"] and not d["private"]:
            fail.append(f"new public declaration without docstring: {d['name']}")
    print()
    code = strip_comments(land_src)
    hits = [w for w in ("sorry", "admit", "native_decide", "axiom ") if re.search(
        r"\b" + w.strip() + r"\b", code)]
    print(f"## Admissions in the landed code (comments stripped): {hits if hits else 'none'}")
    if hits:
        fail.append(f"admissions: {hits}")
    print()
    if fail:
        print("FREEZE: FAIL — " + "; ".join(fail))
        sys.exit(1)
    print(f"FREEZE: PASS — {len(base)} received declarations, every head byte-identical; "
          f"{len(new)} new declarations; header identical; no admission")


if __name__ == "__main__":
    main()
