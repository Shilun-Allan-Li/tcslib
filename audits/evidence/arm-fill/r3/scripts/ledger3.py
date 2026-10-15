"""Round-3 duplication ledger for one tree (base or landed), round 2's conventions kept.

A declaration counts once, with its whole body, if it is the copy side of a counted pair: the
reproducing declaration of an added file, or the added declaration that a library declaration
reproduces. Accountings:
  C   every screen candidate (all classes), same-file pairs included (round 2's A2)
  K   classified, incidental (N) excluded, same-file included (round 2's A4)
  K+  K plus the manual (below-floor) rows present at this tree (round 2's A4+)
Measures per declaration: whole body (characters; code lines) and shared text (largest single
directed overlap over its counted pairs, capped at its body; code lines prorated). Two character
denominators (R2-7): screen-eligible body characters (declarations with a body of at least 60
whitespace-free characters; round 2's 421,911 convention) and all body characters (no floor).
usage: python3 -I ledger3.py <pairs3.tsv> <classify3.tsv> <tree-root> <added.txt> <manual3.tsv> <out-prefix>"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore3 import decls, alldecls, code_lines
ptsv, ctsv, root, added, mtsv, pre = sys.argv[1:7]
new = [l.strip() for l in open(added) if l.strip()]
rows = [c for c in (l.rstrip('\n').split('\t') for l in open(ptsv, encoding='utf-8')) if c[0] != 'pid']
cls = {c[0]: c for c in (l.rstrip('\n').split('\t') for l in open(ctsv, encoding='utf-8')) if c[0] != 'pid'}
info = {}; span = {}; spanall = {}
for p in new:
    txt = open(os.path.join(root, p), encoding='utf-8').read()
    ds = decls(txt); da = alldecls(txt)
    info[p] = dict(elig=sum(d['chars'] for d in ds), allb=sum(d['chars'] for d in da), code=code_lines(txt))
    for d in ds: span[(p, d['name'])] = d
    for d in da: spanall.setdefault((p, d['short']), d)
hits = []
for c in rows:
    A, B = (c[2], c[3]), (c[7], c[8])
    for h in c[12].split('; '):
        d, r = h.split(); sh = int(r.split('/')[0])
        cs = A if (d == 'A>B' or c[1] == 'lib') else B
        hits.append((c[0], cs, sh))
manual = []
for l in open(mtsv, encoding='utf-8'):
    if l.startswith('#') or not l.strip(): continue
    m = l.rstrip('\n').split('\t'); manual.append(m)
PRI = {'D': 0, 'U': 1, 'S:internal': 2, 'S:same': 3, 'G:lib': 4, 'G:internal': 5, 'G:same': 6}
GPRI = {'P1': 0, 'P1+': 1, 'A2a': 2, 'A2w': 3, 'A2b': 4}
def label(pid):
    k = cls[pid]
    return k[2] if k[2] in ('D', 'U') else f'{k[2]}:{k[1]}'
def account(pred, with_manual):
    d = {}
    for pid, cs, sh in hits:
        if not pred(pid): continue
        s = span[cs]; lb = label(pid); g = cls[pid][4]
        cur = d.setdefault(cs, dict(sh=0, lb=lb, g=g, chars=s['chars'], code=s['code'], manual=False))
        cur['sh'] = max(cur['sh'], min(sh, s['chars']))
        if PRI.get(lb, 50) < PRI.get(cur['lb'], 50): cur['lb'] = lb
        if GPRI.get(g, 9) < GPRI.get(cur['g'], 9): cur['g'] = g
    if with_manual:
        for m in manual:
            key = (m[1], m[2])
            s = spanall.get(key)
            assert s, f'manual row not at this tree: {key}'
            ck = (m[1], s['name']) if (m[1], s['name']) in span else key
            cur = d.setdefault(ck, dict(sh=0, lb=m[0], g=m[4], chars=s['chars'], code=s['code'], manual=True))
            cur['sh'] = max(cur['sh'], min(int(m[3]), s['chars']))
            if GPRI.get(m[4], 9) < GPRI.get(cur['g'], 9): cur['g'] = m[4]
    return d
def tot(d, keys=None):
    ks = list(d) if keys is None else keys
    wl = sum(d[k]['code'] for k in ks); wc = sum(d[k]['chars'] for k in ks); sc = sum(d[k]['sh'] for k in ks)
    sl = sum(d[k]['code'] * (d[k]['sh'] / d[k]['chars'] if d[k]['chars'] else 0) for k in ks)
    return dict(n=len(ks), wl=wl, wc=wc, sc=sc, sl=sl)
TE = sum(v['elig'] for v in info.values()); TA = sum(v['allb'] for v in info.values()); TL = sum(v['code'] for v in info.values())
acc = {'C': account(lambda p: True, False), 'K': account(lambda p: cls[p][2] != 'N', False),
       'K+': account(lambda p: cls[p][2] != 'N', True)}
def perfile(d):
    r = {}
    for p in new:
        t = tot(d, [k for k in d if k[0] == p]); i = info[p]
        r[p] = dict(t, wce=t['wc'] / i['elig'] if i['elig'] else 0, wca=t['wc'] / i['allb'] if i['allb'] else 0,
                    wl_=t['wl'] / i['code'], sce=t['sc'] / i['elig'] if i['elig'] else 0,
                    sca=t['sc'] / i['allb'] if i['allb'] else 0, sl_=t['sl'] / i['code'], **i)
    return r
pf = {k: perfile(v) for k, v in acc.items()}
MEAS = [('wce', 'whole body, chars / screen-eligible'), ('wca', 'whole body, chars / all body'),
        ('wl_', 'whole body, code lines'), ('sce', 'shared text, chars / screen-eligible'),
        ('sca', 'shared text, chars / all body'), ('sl_', 'shared text, code lines (prorated)')]
o = open(pre + '.out', 'w', encoding='utf-8'); w = lambda s='': o.write(s + '\n')
w(f'# ledger3 at {root}: 73 added files; denominators: {TL} code lines, {TE} screen-eligible body chars, {TA} all body chars')
w('# accounting | decls | whole-body code lines | whole-body chars (/eligible, /all) | shared chars (/eligible, /all) | shared code lines')
for k, d in acc.items():
    t = tot(d)
    w(f"{k} | {t['n']} | {t['wl']} ({t['wl']/TL:.2%}) | {t['wc']} ({t['wc']/TE:.2%}, {t['wc']/TA:.2%}) | {t['sc']} ({t['sc']/TE:.2%}, {t['sc']/TA:.2%}) | {t['sl']:.0f} ({t['sl']/TL:.2%})")
w('\n## K+ by class (each declaration once, highest class: D > U > S:internal > S:same > G:lib > G:internal > G:same; manual rows by their label)')
by = {}
for k, v in acc['K+'].items(): by.setdefault(v['lb'] + (' (manual)' if v['manual'] else ''), []).append(k)
for lb in sorted(by): t = tot(acc['K+'], by[lb]); w(f"{lb} | {t['n']} | {t['wl']} | {t['wc']} | {t['sc']}")
w('\n## K+ by group (each declaration once, first group in the order P1, P1+, A2a, A2w, A2b)')
by = {}
for k, v in acc['K+'].items(): by.setdefault(v['g'], []).append(k)
for g in sorted(by, key=lambda g: GPRI.get(g, 9)): t = tot(acc['K+'], by[g]); w(f"{g} | {t['n']} | {t['wl']} ({t['wl']/TL:.2%}) | {t['wc']} ({t['wc']/TE:.2%}) | {t['sc']} ({t['sc']/TE:.2%})")
w('\n## Pair counts by category, class and group')
pc = {}
for c in rows: k = (c[1], cls[c[0]][2], cls[c[0]][4]); pc[k] = pc.get(k, 0) + 1
for k in sorted(pc): w(f'{k[0]} {k[1]} {k[2]}: {pc[k]}')
w('\n## Files past one fifth')
lists = {}
for a in acc:
    for m, txt in MEAS:
        L = sorted((p for p, r in pf[a].items() if r[m] > 0.2), key=lambda p: -pf[a][p][m])
        lists[(a, m)] = L
        w(f'{a} {txt}: {len(L)}: ' + ', '.join(f"{p.replace('TCSlib/Complexity/', '')} {pf[a][p][m]:.1%}" for p in L))
w('\n## Per-file (K+): file | code lines | eligible chars | all chars | wb chars/elig | wb chars/all | wb lines | sh chars/elig | sh chars/all | sh lines')
for p in new:
    r = pf['K+'][p]
    if not r['n']: continue
    w(f"{p.replace('TCSlib/Complexity/', '')} | {r['code']} | {r['elig']} | {r['allb']} | {r['wce']:.1%} | {r['wca']:.1%} | {r['wl_']:.1%} | {r['sce']:.1%} | {r['sca']:.1%} | {r['sl_']:.1%}")
with open(pre + '-decls.tsv', 'w', encoding='utf-8') as f:
    f.write('path\tdecl\tlines\tcode_lines\tbody_chars\tshared_chars\tclass\tgroup\tmanual\n')
    for k in sorted(acc['K+']):
        v = acc['K+'][k]; s = span.get(k) or spanall.get(k)
        f.write(f"{k[0]}\t{k[1]}\t{s['l0']}-{s['l1']}\t{v['code']}\t{v['chars']}\t{v['sh']}\t{v['lb']}\t{v['g']}\t{'yes' if v['manual'] else 'no'}\n")
json.dump(dict(totals={k: tot(v) for k, v in acc.items()}, denominators=dict(code=TL, elig=TE, all=TA),
               perfile=pf, lists={f'{a}|{m}': L for (a, m), L in lists.items()}), open(pre + '.json', 'w'), indent=0)
print(open(pre + '.out', encoding='utf-8').read().split('\n## K+ by class')[0])
