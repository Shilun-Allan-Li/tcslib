"""Compare probe outputs, normalized (paths, timing, exit lines, private prefixes stripped)."""
import re, sys
a_dir, b_dir = sys.argv[1:3]
names = sys.argv[3:]
def norm(p):
    out = []
    for l in open(p, encoding='utf-8'):
        l = l.rstrip('\n')
        if l.startswith('# exit') or not l.strip(): continue
        if re.search(r'\breal\b|maximum resident|time:', l): continue
        l = re.sub(r'^\S*?([A-Za-z]+\.lean):', r'\1:', l)
        l = re.sub(r"_private\.\S*?\.0\.", '', l)
        out.append(l)
    return out
for n in names:
    a, b = norm(f'{a_dir}/{n}.out'), norm(f'{b_dir}/{n}.out')
    if a == b: print(f'{n}: identical ({len(a)} lines)')
    else:
        import difflib
        d = [x for x in difflib.unified_diff(a, b, lineterm='', n=0) if x[:1] in '+-' and x[:3] not in ('+++', '---')]
        print(f'{n}: DIFFERS in {len(d)} lines'); print('\n'.join('   ' + x[:160] for x in d[:8]))
