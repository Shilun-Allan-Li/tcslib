#!/usr/bin/env python3
"""Census comparison, base against head, over the declarations of the changed and new modules.

usage: census_diff.py BASE_LOG HEAD_LOG MODULES NAMEMAP

MODULES: one module path per line (TCSlib/.../X, the changed and new files).
NAMEMAP: lines `old<TAB>new` (full names); `old<TAB>-` for a deleted declaration without a
successor. In the base types, every old name is replaced by its new name before comparing, and whitespace is collapsed (the
pretty-printer's line breaks move with the length of a renamed constant), so a
statement that only mentions a renamed constant is not reported as changed (its re-pointing is
listed separately).

Reports:
  REMOVED  base declarations of the modules that are absent at head (by name);
  ADDED    head declarations of the modules that are absent at base;
  CHANGED  declarations present at both whose kind, visibility, reducibility, instance or simp
           status, or type (after the name map) differ;
  REPOINTED declarations whose base type mentions an old name of the map (type equal after it);
  MAP-CHECK every map row: old absent at head, new present at head.
"""
import re, sys

FIELDS = ["mod", "name", "kind", "vis", "red", "inst", "simp", "hash", "type"]


def norm(ty):
    return re.sub(r"\s+", " ", ty).strip()


def load(path):
    d = {}
    for line in open(path):
        if not line.startswith("DECL\t"):
            continue
        p = line.rstrip("\n").split("\t")[1:]
        r = dict(zip(FIELDS, p))
        r["type"] = norm(r["type"])
        d[p[1]] = r
    return d


base, head = load(sys.argv[1]), load(sys.argv[2])
mods = {l.strip().replace("/", ".") for l in open(sys.argv[3]) if l.strip()}
nmap = [tuple(l.rstrip("\n").split("\t")) for l in open(sys.argv[4]) if l.strip() and not l.startswith("#")]
ren = [(o, n) for o, n in nmap if n != "-"]
ren.sort(key=lambda p: -len(p[0]))


def remap(ty):
    for o, n in ren:
        ty = re.sub(r"(?<![\w.'])" + re.escape(o) + r"(?![\w'])", n, ty)
    return ty


bmods = {n: r for n, r in base.items() if r["mod"] in mods}
hmods = {n: r for n, r in head.items() if r["mod"] in mods}
removed = sorted(set(bmods) - set(head) | {n for n in bmods if n in head and head[n]["mod"] not in mods})
added = sorted(set(hmods) - set(base) | {n for n in hmods if n in base and base[n]["mod"] not in mods})
changed, repointed = [], []
for n in sorted(set(bmods) & set(hmods)):
    b, h = bmods[n], hmods[n]
    attrs = [f for f in ("kind", "vis", "red", "inst", "simp") if b[f] != h[f]]
    bt = remap(b["type"])
    if attrs or bt != h["type"]:
        changed.append((n, attrs, b["type"], h["type"]))
    elif b["type"] != h["type"]:
        repointed.append(n)
print(f"# modules compared: {len(mods)}; base decls {len(bmods)}, head decls {len(hmods)}")
print(f"REMOVED {len(removed)}")
for n in removed:
    print(f"  - {n}\t[{bmods[n]['mod']}]")
print(f"ADDED {len(added)}")
for n in added:
    print(f"  + {n}\t[{hmods[n]['mod']}]")
print(f"CHANGED {len(changed)}")
for n, attrs, bt, ht in changed:
    print(f"  ! {n} attrs={attrs}\n      base: {bt}\n      head: {ht}")
print(f"REPOINTED {len(repointed)} (type equal after the name map)")
for n in repointed:
    print(f"  ~ {n}")
bad = 0
print("MAP-CHECK")
for o, n in nmap:
    ok_old = o not in head
    ok_new = n == "-" or n in head
    flag = "ok" if ok_old and ok_new else "BAD"
    bad += flag == "BAD"
    print(f"  {flag}\t{o}\t->\t{n}")
unmapped = [n for n in removed if n not in {o for o, _ in nmap}]
print(f"REMOVED-NOT-IN-MAP {len(unmapped)}")
for n in unmapped:
    print(f"  ? {n}")
print(f"MAP-BAD {bad}")
