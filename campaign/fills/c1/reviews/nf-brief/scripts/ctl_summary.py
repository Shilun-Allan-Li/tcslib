import sys, re
src, out = sys.argv[1], sys.argv[2]
lines = open(src, encoding="utf-8").read().split("\n")
errs = {}
for l in open(out, encoding="utf-8"):
    m = re.match(r'^\S+\.lean:(\d+):(\d+): error: (.*)$', l)
    if m: errs.setdefault(int(m.group(1)), []).append(m.group(3))
sec = None; label = None
rows = []
for i, l in enumerate(lines, 1):
    if l.startswith("section "): sec = l.split()[1]
    if l.startswith("-- "): label = l[3:]
    if l.startswith("example"):
        # find the line where the example ends (line with ':= rfl')
        j = i
        while ":= rfl" not in lines[j-1]: j += 1
        e = [ (n, errs[n]) for n in range(i, j+1) if n in errs]
        rows.append((sec, label, i, j, e))
for sec, label, i, j, e in rows:
    kind = "closes" if not e else "; ".join(f"{n}: {', '.join(m)}" for n, m in e)
    print(f"{sec:18s} | {label:48s} | {i}-{j} | {kind}")
