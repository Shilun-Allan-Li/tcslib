"""Every identifier passed to rw/simp/simpa/dsimp/unfold/simp_rw/erw in lines a..b of a Lean file
(code only), classified with a kinds probe; plus every change/show/rfl/decide/norm_num/infer_instance/
congr/unfold/dsimp site with its line. usage: python3 -I rwargs2.py <file> <a> <b> <kinds out>"""
import re, sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
a, b = int(sys.argv[2]), int(sys.argv[3])
kinds = {}
txt = open(sys.argv[4], encoding='utf-8').read().replace('\n', ' ')
for m in re.finditer(r'KIND (\S+) <- (\S+): (\w+); reducibility \S+; projection (\w+); instance (\w+); matcher (\w+); module some \((\S+)\)', txt):
    kinds[m.group(2)] = (m.group(1), m.group(3), m.group(4) == 'true', m.group(7))
# strip comments/docstrings, keeping line structure
src = '\n'.join(L[a - 1:b]); out, i, depth = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
    out.append(src[i] if depth == 0 else (' ' if src[i] != '\n' else '\n')); i += 1
code = [l.split('--')[0] for l in ''.join(out).split('\n')]
joined = '\n'.join(code)
def lineno(pos): return a + joined.count('\n', 0, pos)
args = []
for m in re.finditer(r'\b(rw|rwa|simp only|simpa only|simp|simpa|dsimp only|dsimp|simp_rw|erw)\s*(\[[^\]]*\])', joined):
    for arg in re.split(r',(?![^\(\)]*\))', m.group(2)[1:-1]):
        arg = re.sub(r'^←\s*', '', arg.strip())
        nm = re.match(r"[A-Za-z_↓][A-Za-z0-9_'.₀-₉]*", arg)
        if nm: args.append((m.group(1), nm.group(0), lineno(m.start())))
own = set(re.findall(r'private (?:theorem|def|instance|lemma) (\S+)', joined))
def cls(n):
    if n in own: return 'own-file private'
    k = kinds.get(n)
    if k is None: return 'local hypothesis / let / core-Mathlib (not a TCSlib constant)'
    full, kind, proj, mod = k
    if not mod.startswith('TCSlib'): return 'non-TCSlib ' + kind
    return 'TCSlib %s%s (%s)' % (kind, ' projection' if proj else '', mod.replace('TCSlib.Complexity.TuringMachine.', ''))
res = {}
for t, n, ln in args: res.setdefault(cls(n), {}).setdefault(n, []).append(ln)
print('rw/simp-family argument occurrences: %d; distinct identifiers: %d' % (len(args), len({n for _, n, _ in args})))
for c in sorted(res):
    print('## %s: %d' % (c, len(res[c])))
    for n in sorted(res[c]): print('   %s  (lines %s)' % (n, ','.join(map(str, sorted(set(res[c][n]))))))
print('\n## definitional-step sites (change/show/rfl/decide/norm_num/infer_instance/congr/unfold/dsimp/simp without only/exact?)')
pat = re.compile(r'\b(change|show|rfl|decide|norm_num|infer_instance|congr|unfold|dsimp|native_decide|simp(?! only)(?!a)|simpa(?! only)|delta|Eq\.mpr|cast)\b')
for i, l in enumerate(code):
    if pat.search(l): print('   %d: %s' % (a + i, l.strip()[:120]))
