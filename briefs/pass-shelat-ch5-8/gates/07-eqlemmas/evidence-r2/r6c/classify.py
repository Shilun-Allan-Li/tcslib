"""classify.py <dir>: (a)/(b) classification of the proof-seal and unfold-scan hits against touched.tsv."""
import re, sys
D = sys.argv[1]
WT = sys.argv[2] if len(sys.argv) > 2 else '/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/wt-e1'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|example|structure)\b\s*([^\s:(\[{]*)')
_cache = {}
def declmap(f):
    """[(start line, full name)] of the declarations of the current file f, namespace-aware."""
    if f in _cache: return _cache[f]
    stack, out = [], []
    for i, l in enumerate(open(f'{WT}/{f}', encoding='utf8').read().split('\n')):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(m.group(1)); continue
        if re.match(r'^section\b', l): stack.append(''); continue
        if re.match(r'^end\b', l):
            if stack: stack.pop()
            continue
        m = DECL.match(l)
        if m:
            n = m.group(2)
            full = n[len('_root_.'):] if n.startswith('_root_.') else '.'.join([x for x in stack if x] + [n])
            out.append((i + 1, full))
    _cache[f] = out; return out
def full_at(f, ln):
    best = None
    for st, full in declmap(f):
        if st <= ln: best = full
    return best
touched = {}
for l in open(D + '/touched.tsv', encoding='utf8'):
    f, d = l.rstrip('\n').split('\t'); kind, rest = d.split(' ', 1); name, ln = rest.rsplit('@', 1)
    touched.setdefault(f, set()).add(full_at(f, int(ln)))
def is_t(f, full):
    return full in touched.get(f, set())
rows = []
for l in open(D + '/proofseal/all.out', encoding='utf8'):
    p = l.rstrip('\n').split('\t')
    if len(p) < 6 or not p[5]: continue
    for item in p[5].split('; '):
        m = re.match(r'(\S+) (\S+)@(\d+) \[(.*)\]', item)
        if m: rows.append(('a' if is_t(p[0], full_at(p[0], int(m.group(3)))) else 'b', 'seal', p[0], m.group(1) + ' ' + m.group(2), 'lines ' + m.group(4)))
sec = None
for l in open(D + '/scan.log', encoding='utf8'):
    if l.startswith('## (c1)'): sec = 'c1'; continue
    if l.startswith('## (c3)'): sec = 'c3'; continue
    if l.startswith('##'): sec = None; continue
    if not sec or l.startswith('#') or not l.strip(): continue
    if sec == 'c1':
        f = l.split(':')[0]; m = re.search(r'\[(\w+) ([^\]]+)\]', l)
        name = m.group(2) if m else '?'; cols = l.rstrip('\n').split('\t')
        rows.append(('a' if is_t(f, full_at(f, int(cols[0].split(':')[1]))) else 'b', 'unfold', f, name, cols[0].split(':')[1] + ' ' + cols[1] + ' ' + cols[4]))
    else:
        p = l.rstrip('\n').split('\t'); f = p[0].replace('.', '/') + '.lean'
        own = re.sub(r'^_private\.[\w.]*?\.0\.', '', p[1])
        while '.' in own and re.fullmatch(r'_\w+|match_\d+|proof_\d+|eq_\d+', own.rsplit('.', 1)[1]):
            own = own.rsplit('.', 1)[0]
        rows.append(('a' if is_t(f, own) else 'b', 'eqn-term', f, p[1], p[3]))
with open(D + '/classified.tsv', 'w') as o:
    for r in rows: o.write('\t'.join(r) + '\n')
na = sum(1 for r in rows if r[0] == 'a'); nb = len(rows) - na
print('a', na, 'b', nb)
for r in rows:
    if r[0] == 'a': print('\t'.join(r)[:260])
