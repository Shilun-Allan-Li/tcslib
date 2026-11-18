# unfoldscan.py <cand-dir> <file>...: names inside unfold/delta/simp/dsimp/rw/simp_rw lists of each
# file that resolve (by full name or last components) to a foreign definition of its seal list.
import re, sys, os
cand, files = sys.argv[1], sys.argv[2:]
tot = 0
for f in files:
    mod = f[:-5].replace('/', '.')
    names = [l.split('\t')[0].strip() for l in open(os.path.join(cand, mod + '.txt')) if l.strip()]
    src = open(f, encoding='utf-8').read()
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    toks = []
    for m in re.finditer(r'\b(unfold|delta|simp only|simp|dsimp only|dsimp|rw|rwa|simp_rw|erw|nth_rw \d+)\s*\[?([^\]\n]*(?:\n\s+[^\]\n]*)*)\]?', src):
        for t in re.split(r'[\s,\[\]←]+', m.group(2)):
            t = t.strip('()')
            if t: toks.append((t, src[:m.start()].count('\n') + 1, m.group(1)))
    hits = []
    for t, line, kw in toks:
        for n in names:
            if n == t or n.endswith('.' + t):
                hits.append((line, kw, t, n))
    tot += len(hits)
    print(f"{f}: {len(hits)} foreign-definition names in unfold/simp/rw lists")
    for h in hits: print("   ", h)
print("total", tot)
