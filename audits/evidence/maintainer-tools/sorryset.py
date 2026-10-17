"""Static base sorry set over an order list (declarations whose comment-stripped text contains
`sorry`), in the brief format `Module: n: names` and a TOTAL line.
Usage: python3 -I sorryset.py <repo root> <order list> <out>"""
import sys, re
root, order, out = sys.argv[1:4]
def strip(src):
    o, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if src.startswith("-/", i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: o.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0] for l in "".join(o).splitlines())
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable)\s+)*)(theorem|lemma|def|abbrev|instance|example|structure)\s+([A-Za-z0-9_.'₀-₉]+)?", re.M)
lines, tot = [], 0
for m in [l.strip() for l in open(order) if l.strip()]:
    s = strip(open(f"{root}/{m}.lean").read())
    ms = list(DECL.finditer(s)); st = [x.start() for x in ms] + [len(s)]
    names = []
    for d, (a, b) in zip(ms, zip(st, st[1:])):
        if re.search(r"\bsorry\b", s[a:b]):
            names.append((d.group(3) or "?") + (" [private]" if "private" in (d.group(1) or "") else ""))
    if names:
        lines.append(f"{m.replace('TCSlib/Complexity/','')}: {len(names)}: {', '.join(names)}"); tot += len(names)
open(out, "w").write("\n".join(lines + [f"TOTAL {tot}"]) + "\n")
print(tot)
