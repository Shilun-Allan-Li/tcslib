"""Name screen (read-only): the declarations of the gate unit, with their namespaces, against
every declaration of the worktree's TCSlib tree.

Usage: python3 -I names.py <unit.lean> [more units ...] <worktree> [--list <out.txt>]

Reports full-name clashes (a clash is an error at landing), duplicates within the units, and,
for information, the existing declarations that share a new declaration's last component in a
namespace that the new modules' consumers open together with `Turing` (the root `Turing`
namespace and `Complexity`), where an unqualified use could become ambiguous. With --list, also
writes the full names of the units' declarations, one per line (the axiom probe reads it).
"""
import os
import re
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*"
                  r"(theorem|lemma|def|structure|abbrev|inductive|instance|class)\s+"
                  r"([A-Za-z0-9_.'«»₀-₉ᵢ-ᵪͰ-Ͽᴀ-ᶿ]+)")


def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
            continue
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if src.startswith("-/", i) and depth > 0:
            depth -= 1; i += 2; continue
        if depth == 0:
            out.append(src[i])
        elif src[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def decls(path):
    stack, res = [], []
    for line in strip(open(path, encoding="utf-8").read()).splitlines():
        if line.startswith(" "):
            continue
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            stack += [("ns", p) for p in m.group(1).split(".")]
            continue
        m = re.match(r"(?:noncomputable\s+)?section\b\s*(\S*)", s)
        if m and s.split()[0] in ("section", "noncomputable"):
            stack.append(("sec", m.group(1)))
            continue
        m = re.match(r"end\b\s*(\S*)$", s)
        if m:
            nm = m.group(1)
            if nm:
                for p in reversed(nm.split(".")):
                    if stack and stack[-1][1] == p:
                        stack.pop()
            elif stack and stack[-1][0] == "sec":
                stack.pop()
            continue
        m = DECL.match(s)
        if m and m.group(1) != "instance":
            n = m.group(2)
            ns = [p for k, p in stack if k == "ns"]
            res.append(n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n]))
    return res


def main():
    args = sys.argv[1:]
    listing, replaced = None, set()
    if "--list" in args:
        k = args.index("--list"); listing = args[k + 1]; args = args[:k] + args[k + 2:]
    if "--replaces" in args:
        k = args.index("--replaces"); replaced = set(args[k + 1].split(","))
        args = args[:k] + args[k + 2:]
    units, root = args[:-1], args[-1]
    mine = [(n, os.path.basename(u)) for u in units for n in decls(u)]
    theirs = {}
    for d, _, fs in os.walk(os.path.join(root, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                for n in decls(p):
                    theirs.setdefault(n, []).append(os.path.relpath(p, root))
    print(f"{len(mine)} declarations in the units; {len(theirs)} distinct declaration names in "
          f"the worktree's TCSlib")
    full = [(n, u, theirs[n]) for n, u in mine if n in theirs and n not in replaced]
    for n in sorted(replaced):
        print(f"  replaced in place, as intended (not a clash): {n} {theirs.get(n)}")
    print(f"full-name clashes with TCSlib: {len(full)}")
    for n, u, w in full:
        print("  CLASH", n, u, w)
    names = [n for n, _ in mine]
    print("duplicates within the units:", sorted({n for n in names if names.count(n) > 1}))
    last = {}
    for n in theirs:
        last.setdefault(n.split(".")[-1], []).append(n)
    print("same last component, in `Turing` or `Complexity` directly (possible ambiguity under "
          "`open Turing` inside `namespace Complexity`):")
    hits = 0
    for n, _ in mine:
        for o in last.get(n.split(".")[-1], []):
            if o.count(".") == 1 and o.split(".")[0] in ("Turing", "Complexity") and o != n:
                print(f"  {n} ~ {o}"); hits += 1
    print(f"  ({hits})")
    print("same last component elsewhere (information; distinct namespaces):")
    for n, _ in mine:
        others = [o for o in last.get(n.split(".")[-1], []) if o != n]
        if others:
            print(f"  {n}: {', '.join(sorted(others)[:6])}{' …' if len(others) > 6 else ''}")
    if listing:
        open(listing, "w", encoding="utf-8").write("\n".join(names) + "\n")


if __name__ == "__main__":
    main()
