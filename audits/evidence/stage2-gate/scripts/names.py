"""Name screen (read-only): the declarations of the gate units, with their namespaces, against
every declaration of the worktree's TCSlib tree (full names; and short names declared in the
namespaces that the vendored compiler files open)."""
import os, re, sys
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?(?:noncomputable\s+)?"
                  r"(theorem|lemma|def|structure|abbrev|inductive|instance)\s+([A-Za-z0-9_.'«»]+)")
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if src.startswith("-/", i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0] for l in "".join(out).splitlines())
def decls(path):
    ns, res = [], []
    for line in strip(open(path, encoding="utf-8").read()).splitlines():
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m: ns.append(m.group(1)); continue
        m = re.match(r"end\s+(\S+)", s)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = DECL.match(s)
        if m:
            n = m.group(2)
            n = n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n])
            res.append(n)
    return res
units, root = sys.argv[1:-1], sys.argv[-1]
mine = []
for u in units:
    mine += [(n, os.path.basename(u)) for n in decls(u)]
theirs = {}
for d, _, fs in os.walk(os.path.join(root, "TCSlib")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(d, f)
            for n in decls(p):
                theirs.setdefault(n, []).append(os.path.relpath(p, root))
full = [(n, u, theirs[n]) for n, u in mine if n in theirs]
print(f"{len(mine)} declarations in the units; full-name clashes with TCSlib: {len(full)}")
for n, u, w in full: print("  CLASH", n, u, w)
# short names that the vendored compiler would see unqualified through `open WordRAM`
opened = {}
for n, ps in theirs.items():
    if n.startswith("Light.Compiler.") or n.startswith("Light."):
        opened.setdefault(n.split(".")[-1], []).append(n)
short = [(n, opened[n.split(".")[-1]]) for n, u in mine
         if n.startswith("WordRAM.") and n.count(".") == 1 and n.split(".")[-1] in opened]
print(f"WordRAM short names that also name a Light or Light.Compiler declaration: {len(short)}")
for n, w in short: print("  SHORT", n, w)
dup = sorted({n for n, _ in mine if [m for m, _ in mine].count(n) > 1})
print("duplicates within the units:", dup)
