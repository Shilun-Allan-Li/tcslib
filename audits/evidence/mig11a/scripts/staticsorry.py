"""Static sorry count per module (declarations whose comment-stripped text contains the token
`sorry`), compared with a replay log's per-module counts. Usage:
python3 -I staticsorry.py <repo root> <replay log>"""
import sys, re
root, log = sys.argv[1:3]
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if src.startswith("-/", i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0] for l in "".join(out).splitlines())
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|instance|example|structure|inductive)\b", re.M)
bad = 0; n = 0; tot = 0
for l in open(log):
    m = re.match(r"(\S+) exit=\d+ errors=\d+ sorry=(\d+)", l)
    if not m: continue
    mod, k = m.group(1), int(m.group(2))
    s = strip(open(f"{root}/{mod}.lean").read())
    starts = [x.start() for x in DECL.finditer(s)] + [len(s)]
    c = sum(1 for a, b in zip(starts, starts[1:]) if re.search(r"\bsorry\b", s[a:b]))
    n += 1; tot += c
    if c != k: bad += 1; print("MISMATCH", mod, "static", c, "replay", k)
print(f"modules {n}, mismatches {bad}, static total {tot}")
