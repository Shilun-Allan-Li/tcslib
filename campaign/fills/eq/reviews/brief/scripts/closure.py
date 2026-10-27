import sys, os, re
root = sys.argv[1]; start = sys.argv[2:]
seen = set(); stack = list(start)
while stack:
    m = stack.pop()
    if m in seen: continue
    seen.add(m)
    if not m.startswith("TCSlib"): continue
    p = os.path.join(root, m.replace(".", "/") + ".lean")
    if not os.path.exists(p): print("MISSING", m); continue
    for line in open(p, encoding="utf-8"):
        mm = re.match(r"^import\s+(\S+)", line)
        if mm: stack.append(mm.group(1))
for m in sorted(seen):
    if m.startswith("TCSlib"): print(m)
