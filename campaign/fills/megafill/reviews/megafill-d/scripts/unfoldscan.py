"""For line ranges of a file, list the identifiers passed to simp/simp only/unfold/rw/dsimp/simpa
(their bracket lists, or unfold's arguments) whose last component is the last component of some
TCSlib `def`/`abbrev` (any file). Approximate (name-based). Usage: unfoldscan.py <wt> <file> <name:a-b>..."""
import os, re, sys
wt, f, specs = sys.argv[1], sys.argv[2], sys.argv[3:]
defs = {}
for dp, dn, fn in os.walk(os.path.join(wt, "TCSlib")):
    for x in fn:
        if x.endswith(".lean"):
            p = os.path.join(dp, x)
            for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev)\s+([A-Za-z0-9_.'«»]+)", open(p, encoding="utf-8").read(), re.M):
                defs.setdefault(m.group(1).rsplit(".", 1)[-1].replace("_root_.", ""), set()).add(os.path.relpath(p, wt))
lines = open(os.path.join(wt, f), encoding="utf-8").read().split("\n")
for s in specs:
    name, rng = s.split(":")
    a, b = map(int, rng.split("-"))
    body = "\n".join(lines[a - 1 : b])
    hits = {}
    for m in re.finditer(r"\b(?:simp only|simp|dsimp only|dsimp|simpa only|simpa|rw|rwa|unfold)\b\s*(\[[^\]]*\]|[^\n]*)", body):
        arg = m.group(1)
        for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", arg):
            last = tok.rsplit(".", 1)[-1]
            if last in defs and last not in ("at", "using", "only"):
                hits[tok] = hits.get(tok, 0) + 1
    print(f"{name} ({a}-{b}): " + (", ".join(f"{k} x{v} [{'/'.join(sorted(defs[k.rsplit('.',1)[-1]]))[:80]}]" for k, v in sorted(hits.items())) or "none"))
