"""Import graph of a worktree's TCSlib modules. Usage:
  importgraph.py <wt> up <mod>...        : the import closure (ancestors) of the modules
  importgraph.py <wt> down <mod>...      : the downstream closure (importers), the root TCSlib excluded
Modules are dotted names; output one per line, sorted."""
import os, re, sys
wt, mode, mods = sys.argv[1], sys.argv[2], sys.argv[3:]
imps = {}
for dp, dn, fn in os.walk(os.path.join(wt, "TCSlib")):
    for f in fn:
        if f.endswith(".lean"):
            p = os.path.join(dp, f)
            m = os.path.relpath(p, wt)[:-5].replace(os.sep, ".")
            imps[m] = [mm.group(1) for line in open(p, encoding="utf-8")
                       for mm in [re.match(r"^import\s+(\S+)", line.strip())] if mm and mm.group(1).startswith("TCSlib")]
for m in mods:
    assert m in imps, m
if mode == "up":
    seen, st = set(), list(mods)
    while st:
        m = st.pop()
        for i in imps.get(m, []):
            if i not in seen:
                seen.add(i); st.append(i)
else:
    rev = {}
    for m, l in imps.items():
        for i in l:
            rev.setdefault(i, []).append(m)
    seen, st = set(), list(mods)
    while st:
        m = st.pop()
        for i in rev.get(m, []):
            if i not in seen and i != "TCSlib":
                seen.add(i); st.append(i)
for m in sorted(seen):
    print(m)
