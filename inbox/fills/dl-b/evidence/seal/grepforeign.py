# usage: python3 -I grepforeign.py <diff file> <sealed names> -- foreign definitions inside
# simp / simp only / rw / rewrite / unfold / dsimp / delta lists of the added lines
import re, sys
diff = open(sys.argv[1]).read().splitlines()
names = [l.strip() for l in open(sys.argv[2]) if l.strip()]
short = {}
for nm in names:
    short.setdefault(nm.split('.')[-1], []).append(nm)
    short.setdefault(nm, []).append(nm)
    parts = nm.split('.')
    for k in range(1, len(parts)):
        short.setdefault('.'.join(parts[k:]), []).append(nm)
added = "\n".join(l[1:] for l in diff if l.startswith('+') and not l.startswith('+++'))
lists = []
for m in re.finditer(r'\b(simp only|simp_rw|simp|rw|rewrite|dsimp only|dsimp|nth_rewrite \d+|nth_rw \d+)\s*\[', added):
    i = m.end(); depth = 1; j = i
    while depth and j < len(added):
        if added[j] == '[': depth += 1
        elif added[j] == ']': depth -= 1
        j += 1
    lists.append((m.group(1), added[i:j-1]))
for m in re.finditer(r'\b(unfold|delta)\s+([^\n]*)', added):
    lists.append((m.group(1), m.group(2)))
hits = []
for kind, body in lists:
    for tok in re.split(r'[\s,\[\]()←]+', body):
        tok = tok.strip()
        if tok in short:
            hits.append((kind, tok, body.replace('\n', ' ')[:160]))
print(f"tactic lists scanned: {len(lists)}")
print(f"foreign definition names used as rewrite/unfold rules: {len(hits)}")
for h in hits:
    print("HIT", h)
