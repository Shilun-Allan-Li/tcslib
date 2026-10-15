import json, re, sys, difflib, collections
C = sys.argv[1]
files = {'Composition': 'TuringMachine/Composition.lean', 'Primitives': 'TuringMachine/Build/Primitives.lean',
         'Loop': 'TuringMachine/Build/Loop.lean', 'Wrappers': 'TuringMachine/Build/Wrappers.lean',
         'TimeConstructible': 'ClassP/TimeConstructible.lean', 'Encoding': 'TuringMachine/Encoding.lean',
         'Simulation': 'TuringMachine/Simulation.lean', 'Catalog': 'TuringMachine/Build/Catalog.lean'}
src = {k: open(C + '/' + v, encoding='utf-8').read().split('\n') for k, v in files.items()}
decl = {k: json.load(open('d_' + k + '.json')) for k in files}
def with_doc(lines, d):
    # extend start upward over an immediately preceding docstring /-- ... -/ and attributes
    s = d['line'] - 1
    j = s - 1
    while j >= 0 and lines[j].startswith('@['): j -= 1
    if j >= 0 and lines[j].rstrip().endswith('-/'):
        k = j
        while k >= 0 and not lines[k].lstrip().startswith('/--'): k -= 1
        if k >= 0: s = k
    return s, d['end']  # 0-based start, 1-based end (exclusive in 0-based)
idx = {}
for k in files:
    if k == 'Catalog': continue
    for d in decl[k]: idx.setdefault(d['name'], []).append((k, d))
def norm(l): return l.replace('f2_', '').rstrip()
tot_lines = tot_doc = 0; ver = verd = 0; nsrc = 0
per = []
for d in decl['Catalog']:
    if not d['name'].startswith('f2_'): continue
    s, e = with_doc(src['Catalog'], d)
    a = src['Catalog'][s:e]; ab = src['Catalog'][d['line'] - 1:e]
    tot_lines += len(ab); tot_doc += len(a)
    base = d['name'][3:]
    m = 0; md = 0; where = None
    if base in idx:
        k, sd = idx[base][0]; where = k; nsrc += 1
        ss, se = with_doc(src[k], sd)
        b = src[k][ss:se]; bb = src[k][sd['line'] - 1:se]
        sm = difflib.SequenceMatcher(None, [norm(x) for x in a], [x.rstrip() for x in b], autojunk=False)
        md = sum(t.size for t in sm.get_matching_blocks())
        sm2 = difflib.SequenceMatcher(None, [norm(x) for x in ab], [x.rstrip() for x in bb], autojunk=False)
        m = sum(t.size for t in sm2.get_matching_blocks())
    ver += m; verd += md
    per.append((d['line'], d['name'], where, len(ab), m, len(a), md))
print(f'f2 decls {len(per)}; with same-named source {nsrc}')
print(f'lines (code only) {tot_lines}; verbatim-matched code lines {ver}')
print(f'lines (with docstrings) {tot_doc}; verbatim-matched incl. docstrings {verd}')
json.dump(per, open('verbatim.json', 'w'))
c = collections.Counter(); cl = collections.Counter()
for p in per: c[p[2]] += 1; cl[p[2]] += p[6]
print(c); print(cl)
