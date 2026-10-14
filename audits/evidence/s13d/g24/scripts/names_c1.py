"""Name screen for the C1 hosts unit (read-only; standard library only).

Usage: python3 -I names_c1.py <unit.lean> <worktree> [<pending unit> ...]

1. Every declaration of the unit (full name, namespaces resolved) against every declaration of
   the worktree's TCSlib tree.
2. The same against the pending statement units given (other gates' drafts), which land in
   parallel; an intended shared name is reported, not hidden.
3. Short names: a unit declaration whose last component is also the last component of a
   declaration in a namespace that a downstream TCSlib file opens together with the unit's
   namespace (reported for review; not a clash by itself).
"""
import os
import re
import sys

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(private\s+)?(?:noncomputable\s+)?"
                  r"(theorem|lemma|def|structure|abbrev|inductive|instance)\s+([A-Za-z0-9_.'«»₀-₉]+)")


def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0] for l in "".join(out).splitlines())


def decls(path):
    ns, res = [], []
    for line in strip(open(path, encoding="utf-8").read()).splitlines():
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            ns.append(m.group(1))
            continue
        m = re.match(r"end\s+(\S+)", s)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            continue
        m = DECL.match(s)
        if m:
            n = m.group(3)
            n = n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n])
            res.append((n, bool(m.group(1))))
    return res


def main():
    unit, root, pending = sys.argv[1], sys.argv[2], sys.argv[3:]
    mine = decls(unit)
    pub = [n for n, p in mine if not p]
    priv = [n for n, p in mine if p]
    print(f"{len(mine)} declarations in the unit ({len(pub)} public, {len(priv)} private)")
    theirs = {}
    for d, _, fs in os.walk(os.path.join(root, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                for n, _ in decls(p):
                    theirs.setdefault(n, []).append(os.path.relpath(p, root))
    full = [(n, theirs[n]) for n, _ in mine if n in theirs]
    print(f"1. full-name clashes with the TCSlib tree: {len(full)}")
    for n, w in full:
        print("   CLASH", n, w)
    for u in pending:
        names = {n for n, _ in decls(u)}
        hits = sorted(n for n, _ in mine if n in names)
        print(f"2. shared with {os.path.relpath(u, root)}: {len(hits)}" +
              (": " + ", ".join(hits) if hits else ""))
    short = {}
    for n in theirs:
        short.setdefault(n.split(".")[-1], set()).add(n)
    amb = []
    for n in pub:
        others = sorted(m for m in short.get(n.split(".")[-1], ()) if m != n)
        if others:
            amb.append((n, others))
    print(f"3. unit public names whose last component also names another TCSlib declaration: "
          f"{len(amb)}")
    for n, o in amb:
        print("   SHORT", n, "~", ", ".join(o[:4]) + (" …" if len(o) > 4 else ""))
    dup = sorted({n for n, _ in mine if [m for m, _ in mine].count(n) > 1})
    print("4. duplicates within the unit:", dup)


if __name__ == "__main__":
    main()
