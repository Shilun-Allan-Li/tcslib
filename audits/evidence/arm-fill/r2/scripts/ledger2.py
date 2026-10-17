"""Round-2 duplication ledger (ARM fill gate), same-file pairs included and classified.

Inputs (all read-only): the round-1 combined screen output over flattened copies, its labels,
the added-file list, the round-1 screen root (byte copies at the received tree), pairs.tsv and
classify.tsv (this round's), the global import order (round 1's root-up.txt), and manual.tsv
(below-floor entries, kept visible). Declaration spans and body measure: round 1's ledger.py.

Accountings (a declaration is counted once, with its whole body, if it is the copy side of at
least one counted pair; copy side = round 1's rule: the reproducing declaration of an added
file, or the added declaration that a library declaration reproduces):
  A1 cross-file pairs, every screen candidate (round 1's ledger; reproduction check)
  A2 A1 plus same-file pairs, every candidate (the round-1 auditor's broadened screen)
  A3 cross-file pairs, classified, incidental (N) excluded
  A4 A3 plus same-file pairs, classified, N excluded  <- the ledger proposed for acknowledgement
  A4+ A4 plus the manual below-floor entries
Measures per declaration: whole body (characters; code lines) and shared text (largest single
directed overlap over its counted pairs, capped at the body; code lines prorated by
shared/body). Shares are of the 73 files' 421,911 body characters / 17,227 code lines.
usage: python3 -I ledger2.py <screen.out> <labels> <added> <screen-root> <pairs.tsv>
       <classify.tsv> <order.txt> <manual.tsv> <outdir>"""
import os, re, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines, DECL, body
out, labels, added, sroot, ptsv, ctsv, ordf, mtsv, odir = sys.argv[1:10]
lab = {}
for l in open(labels, encoding='utf-8'):
    a, p, _ = l.rstrip('\n').split('\t'); lab[a] = p
new = {l.strip() for l in open(added) if l.strip()}
spans = {}; fileinfo = {}
for flat, path in lab.items():
    t = strip_keep_lines(open(os.path.join(sroot, flat), encoding='utf-8').read())
    ms = list(DECL.finditer(t)); total_chars = 0
    code_lines = sum(1 for l in t.split('\n') if l.strip())
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        seg = t[m.start():end]
        bd = re.sub(r'\s+', '', body(seg))
        l0 = t.count('\n', 0, m.start()) + 1
        l1 = l0 + seg.rstrip().count('\n')
        cl = sum(1 for l in seg.split('\n') if l.strip())
        if len(bd) >= 60: total_chars += len(bd)
        spans.setdefault((path, m.group(3)), []).append((l0, l1, cl, len(bd)))
    fileinfo[path] = dict(chars=total_chars, code=code_lines)
def sp(k):
    s = spans.get(k); return s[0] if s else None
cls = {}
for l in open(ctsv, encoding='utf-8'):
    c = l.rstrip('\n').split('\t')
    if c[0] == 'pid': continue
    cls[c[0]] = (c[1], c[2], c[3], c[4])
P = re.compile(r'^\s+(\S+?)::(\S+)\s+reproduces\s+(\S+?)::(\S+): (\d+)/(\d+) = (\d+)%')
pid_of = {}
for l in open(ptsv, encoding='utf-8'):
    c = l.rstrip('\n').split('\t')
    if c[0] == 'pid': continue
    pid_of[frozenset([(c[2], c[3]), (c[7], c[8])])] = c[0]
hits = []   # (pid, copyside key, shared)
for l in open(out, encoding='utf-8'):
    m = P.match(l)
    if not m: continue
    fa, a, fb, b, sh, ln, pct = m.groups()
    pa, pb = lab[fa], lab[fb]
    if pa not in new and pb not in new: continue
    pid = pid_of[frozenset([(pa, a), (pb, b)])]
    cs = (pa, a) if pa in new else (pb, b)
    hits.append((pid, cs, int(sh)))
assert len(hits) == 512, len(hits)
manual = []
for l in open(mtsv, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    c = l.rstrip('\n').split('\t'); manual.append(c)
TOT_C = sum(fileinfo[p]['chars'] for p in new); TOT_L = sum(fileinfo[p]['code'] for p in new)
PRI = {'D': 0, 'U': 1, 'S:internal': 2, 'S:same': 3, 'G:lib': 4, 'G:internal': 5, 'G:same': 6,
       'N:lib': 7, 'N:internal': 8, 'N:same': 9}
def label(pid):
    cat, c, _, _ = cls[pid]
    if c in ('D', 'U'): return c
    return f'{c}:{cat}'
def account(pred, extra=()):
    """decl -> (shared, best label); pred(pid) selects counted pairs; extra = manual decls"""
    d = {}
    for pid, cs, sh in hits:
        if not pred(pid): continue
        lb = label(pid); s = sp(cs)
        cur = d.get(cs)
        shc = min(sh, s[3])
        if cur is None: d[cs] = [shc, lb]
        else:
            cur[0] = max(cur[0], shc)
            if PRI[lb] < PRI[cur[1]]: cur[1] = lb
    for key, shc, lb in extra:
        s = sp(key)
        cur = d.get(key)
        if cur is None: d[key] = [min(shc, s[3]), lb]
        else:
            cur[0] = max(cur[0], min(shc, s[3]))
            if PRI.get(lb, 99) < PRI.get(cur[1], 99): cur[1] = lb
    return d
def meas(d, keys=None):
    keys = list(d) if keys is None else keys
    wl = sum(sp(k)[2] for k in keys); wc = sum(sp(k)[3] for k in keys)
    sc = sum(d[k][0] for k in keys)
    sl = sum(sp(k)[2] * (d[k][0] / sp(k)[3] if sp(k)[3] else 0) for k in keys)
    return len(keys), wl, wc, sc, sl
def perfile(d):
    res = {}
    for p in sorted(new):
        ks = [k for k in d if k[0] == p]
        n, wl, wc, sc, sl = meas(d, ks); fi = fileinfo[p]
        res[p] = dict(n=n, wl=wl, wc=wc, sc=sc, sl=sl, pwc=wc / fi['chars'], pwl=wl / fi['code'],
                      psc=sc / fi['chars'], psl=sl / fi['code'], chars=fi['chars'], code=fi['code'])
    return res
man_extra = []; man_grp = {}
for c in manual:
    key = (c[1], c[2]); assert sp(key), key
    man_extra.append((key, int(c[3]), c[0])); man_grp[key] = c[4]
GPRI = {'P1': 0, 'P1+': 1, 'A2a': 2, 'A2b': 3}
def groups(d):
    g = {}
    for pid, cs, sh in hits:
        if cs not in d or cls[pid][1] == 'N': continue
        gg = cls[pid][3]
        if cs not in g or GPRI[gg] < GPRI[g[cs]]: g[cs] = gg
    for k, gg in man_grp.items():
        if k in d and (k not in g or GPRI[gg] < GPRI[g[k]]): g[k] = gg
    return g
acc = {
 'A1': account(lambda pid: cls[pid][0] != 'same'),
 'A2': account(lambda pid: True),
 'A3': account(lambda pid: cls[pid][0] != 'same' and cls[pid][1] != 'N'),
 'A4': account(lambda pid: cls[pid][1] != 'N'),
}
acc['A4+'] = account(lambda pid: cls[pid][1] != 'N', man_extra)
pf = {k: perfile(v) for k, v in acc.items()}
o = open(os.path.join(odir, 'ledger2.out'), 'w', encoding='utf-8')
def w(s=''): o.write(s + '\n')
w(f'# ledger2: denominators over the 73 added files: {TOT_L} code lines, {TOT_C} body characters')
w('# accounting | declarations | whole-body code lines (share) | whole-body chars (share) | shared-text chars (share) | shared-text code lines, prorated (share)')
for k, d in acc.items():
    n, wl, wc, sc, sl = meas(d)
    w(f'{k} | {n} | {wl} ({wl/TOT_L:.2%}) | {wc} ({wc/TOT_C:.2%}) | {sc} ({sc/TOT_C:.2%}) | {sl:.0f} ({sl/TOT_L:.2%})')
w('\n## A4+ by class (each declaration once, under its highest class: D > U > S:internal > S:same > G:lib > G:internal > G:same; manual entries M*)')
bycls = {}
for k, (shc, lb) in acc['A4+'].items(): bycls.setdefault(lb, []).append(k)
for lb in sorted(bycls, key=lambda x: PRI.get(x, 50)):
    n, wl, wc, sc, sl = meas(acc['A4+'], bycls[lb])
    w(f'{lb} | {n} decls | {wl} code lines ({wl/TOT_L:.2%}) | {wc} chars ({wc/TOT_C:.2%}) | shared {sc} ({sc/TOT_C:.2%}) | shared lines {sl:.0f}')
grp = groups(acc['A4+'])
w('\n## A4+ by group (user dedup decisions; each declaration once, under its first group in the order P1, P1+, A2a, A2b)')
for gg in ('P1', 'P1+', 'A2a', 'A2b'):
    ks = [k for k in acc['A4+'] if grp.get(k) == gg]
    n, wl, wc, sc, sl = meas(acc['A4+'], ks)
    w(f'{gg} | {n} decls | {wl} code lines ({wl/TOT_L:.2%}) | {wc} chars ({wc/TOT_C:.2%}) | shared {sc} ({sc/TOT_C:.2%}) | shared lines {sl:.0f}')
assert all(k in grp for k in acc['A4+']), [k for k in acc['A4+'] if k not in grp]
w('\n## Pair counts by category, class and group (unordered)')
pc = {}
for pid, (cat, c, fam, g) in cls.items(): pc[(cat, c, g)] = pc.get((cat, c, g), 0) + 1
for k in sorted(pc): w(f'{k[0]} {k[1]} {k[2]}: {pc[k]}')
MEAS = [('pwc', 'whole body, characters'), ('pwl', 'whole body, code lines'),
        ('psc', 'shared text, characters'), ('psl', 'shared text, code lines (prorated)')]
w('\n## Files past one fifth, per accounting and measure')
over = {}
for k in pf:
    for m, txt in MEAS:
        over[(k, m)] = sorted(p for p, r in pf[k].items() if r[m] > 0.2)
        w(f'{k} {txt}: {len(over[(k, m)])}')
w('\n## A4 (the classified ledger with same-file pairs) against round 1 (A1) and against A3, per measure')
for m, txt in MEAS:
    a4, a1, a3 = set(over[('A4', m)]), set(over[('A1', m)]), set(over[('A3', m)])
    sh = lambda s: ', '.join(x.replace('TCSlib/Complexity/', '') for x in sorted(s)) or '(none)'
    w(f'- {txt}: A4 {len(a4)} files; newly past vs round 1 (A1): {sh(a4 - a1)}; no longer past vs A1 (only incidental pairs had taken them over): {sh(a1 - a4)}; newly past vs A3 (same-file pairs alone): {sh(a4 - a3)}')
w('\n## Per-file table (A1 | A3 | A4 | A4+): whole-body chars %, whole-body lines %, shared chars %, shared lines %')
for p in sorted(new):
    r = [pf[k][p] for k in ('A1', 'A3', 'A4', 'A4+')]
    if not any(x['n'] for x in r): continue
    w(f'{p.replace("TCSlib/Complexity/","")} | chars {r[0]["chars"]} lines {r[0]["code"]} | ' + ' | '.join(
        f'{x["pwc"]:.1%} {x["pwl"]:.1%} {x["psc"]:.1%} {x["psl"]:.1%}' for x in r))
# net view (convention): components over counted internal + same-file edges among added decls
order = {l.strip() + '.lean': i for i, l in enumerate(open(ordf)) if l.strip()}
adj = {}
pairs_rows = [l.rstrip('\n').split('\t') for l in open(ptsv, encoding='utf-8')][1:]
for c in pairs_rows:
    if c[1] == 'lib' or cls[c[0]][1] == 'N': continue
    A, B = (c[2], c[3]), (c[7], c[8])
    adj.setdefault(A, set()).add(B); adj.setdefault(B, set()).add(A)
seen = set(); comps = []
for v in adj:
    if v in seen: continue
    st = [v]; comp = []; seen.add(v)
    while st:
        u = st.pop(); comp.append(u)
        for x in adj[u]:
            if x not in seen: seen.add(x); st.append(x)
    comps.append(comp)
netkeys = {k for k, (s, lb) in acc['A4+'].items() if lb in ('D', 'U', 'G:lib') or lb.startswith('M')}
for comp in comps:
    comp.sort(key=lambda k: (order.get(k[0], 10**9), sp(k)[0]))
    netkeys.update(k for k in comp[1:] if k in acc['A4+'])
n, wl, wc, sc, sl = meas(acc['A4+'], list(netkeys))
w(f'\n## Net view of A4+ (accounting convention only: one member of each internal/same-file component, earliest in import order, treated as the original): {len(comps)} components; {n} declarations, {wl} code lines ({wl/TOT_L:.2%}), {wc} chars ({wc/TOT_C:.2%}), shared {sc} ({sc/TOT_C:.2%})')
# export the A4+ declaration table
with open(os.path.join(odir, 'ledger2-decls.tsv'), 'w', encoding='utf-8') as f:
    f.write('path\tdecl\tlines\tcode_lines\tbody_chars\tshared_chars\tclass\tgroup\n')
    for k in sorted(acc['A4+']):
        s = sp(k); shc, lb = acc['A4+'][k]
        f.write(f'{k[0]}\t{k[1]}\t{s[0]}-{s[1]}\t{s[2]}\t{s[3]}\t{shc}\t{lb}\t{grp[k]}\n')
json.dump({k: {p: v for p, v in pf[k].items()} for k in pf}, open(os.path.join(odir, 'ledger2-perfile.json'), 'w'), indent=0)
print('written')
