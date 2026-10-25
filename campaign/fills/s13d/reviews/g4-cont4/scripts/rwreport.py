import sys, json, re
from collections import Counter, defaultdict
calls = json.load(open(sys.argv[1])); ids = json.load(open(sys.argv[2]))
kinds = {}
for l in open(sys.argv[3], encoding='utf-8'):
    m = re.search(r'RVK (\S+) \| (.*)', l)
    if not m: continue
    parts = [p.strip() for p in m.group(2).split(' | ')]
    if parts[0] == 'unresolved': kinds[m.group(1)] = ('unresolved',); continue
    kinds[m.group(1)] = (parts[0], parts[2], parts[3], parts[4], parts[7], parts[9])  # full, module, kind, red, simpUnfold, simproc
own = set(ids['own'])
def split_top(s):
    out, d, cur = [], 0, ''
    for ch in s:
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        if ch == ',' and d == 0: out.append(cur); cur = ''
        else: cur += ch
    if cur.strip(): out.append(cur)
    return [e.strip() for e in out]
IDH = re.compile(r"^(?:←\s*|<-\s*)?([A-Za-z_Ͱ-Ͽ][\w.'Ͱ-Ͽ₀-₉!?]*)")
rule_rows = []; mention_rows = []
for c in calls:
    if c['kind'] == 'list':
        for e in split_top(c['args']):
            m = IDH.match(e)
            if not m: continue
            h = m.group(1)
            rule_rows.append((c['line'], c['tac'], h, e[:80]))
    elif c['kind'] == 'unfold':
        for h in c['args'].split():
            rule_rows.append((c['line'], c['tac'], h, h))
    elif c['kind'] == 'term':
        for h in c['ids']: mention_rows.append((c['line'], c['tac'], h))
def cls(h):
    if h in own or h.split('.')[0] in own: return 'own'
    k = kinds.get(h)
    if k is None:
        # dotted local projection like hp.1 or h.symm
        base = h.split('.')[0]
        return 'local' if base not in kinds else ('local' if kinds[base][0] == 'unresolved' else 'dotted')
    if k[0] == 'unresolved': return 'local'
    full, mod, kind, red, su, sp = k
    tcs = mod.startswith('TCSlib')
    if sp == 'simproc=true': return 'simproc:' + full
    if kind in ('def', 'opaque'):
        return ('TCSLIB-DEF:' if tcs else 'CORE/MATHLIB-DEF:') + full
    return ('tcslib-' if tcs else 'core/mathlib-') + kind
cnt = Counter(); bad = defaultdict(list)
for line, tac, h, e in rule_rows:
    k = cls(h); cnt[k.split(':')[0]] += 1
    if k.startswith(('TCSLIB-DEF', 'CORE/MATHLIB-DEF', 'simproc')): bad[k].append((line, tac, e))
print('rule elements (rw/rwa/simp/simpa/dsimp lists and unfold args) on added lines:', len(rule_rows))
for k, v in sorted(cnt.items()): print(f'  {k}: {v}')
print('definitions or simprocs used as a rule:')
for k, v in bad.items():
    print(f'  {k}: {len(v)} occurrence(s)')
    for x in v[:12]: print('     ', x)
mc = Counter(); mdefs = defaultdict(list)
for line, tac, h in mention_rows:
    k = cls(h)
    if k.startswith(('TCSLIB-DEF', 'CORE/MATHLIB-DEF')): mdefs[k].append(line)
    mc[k.split(':')[0]] += 1
print('show/change term identifiers:', len(mention_rows), dict(mc))
print('definitions mentioned in show/change terms (allowed; covered by the seal):')
for k, v in sorted(mdefs.items()): print(f'  {k}: {len(v)} (lines {v[:8]}...)')
# definitions mentioned inside rw/simp list elements but not as the head
inner = defaultdict(list)
for c in calls:
    if c['kind'] != 'list': continue
    for e in split_top(c['args']):
        m = IDH.match(e); h = m.group(1) if m else None
        for i in re.findall(r"[A-Za-z_][\w.'₀-₉]*", e):
            if i == h: continue
            k = cls(i)
            if k.startswith(('TCSLIB-DEF', 'CORE/MATHLIB-DEF')): inner[k].append((c['line'], e[:70]))
print('definitions inside a list element but not its head (term arguments, show ... by ...):')
for k, v in sorted(inner.items()): print(f'  {k}: {len(v)}; e.g. {v[:2]}')
