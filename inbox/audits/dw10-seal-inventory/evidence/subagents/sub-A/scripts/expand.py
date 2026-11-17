"""Expand sub-A decisions (work/decisions.tsv) into overrides-A.tsv, one row per open item."""
import collections

EV = '/home/user/dw10/sub/snap-r1'
OUT = '/home/user/dw10/exch/inbox/audits/dw10-seal-inventory/evidence/subagents/sub-A'

rows = []
with open(f'{EV}/review/open-items.tsv') as f:
    hdr = f.readline().rstrip('\n').split('\t')
    for line in f:
        d = dict(zip(hdr, line.rstrip('\n').split('\t')))
        if d['agent'] == 'sub-A':
            rows.append(d)

dec = {}
for line in open(f'{OUT}/work/decisions.tsv'):
    if line.startswith('#') or not line.strip():
        continue
    p = line.rstrip('\n').split('\t')
    assert len(p) == 5, (len(p), line[:120])
    if p[0] in dec:
        raise SystemExit('duplicate selector ' + p[0])
    dec[p[0]] = p[1:]

CLASSES = {'STAGE2', 'STAGE2-PROVIDER-READER', 'SEAL-B-ONLY', 'STRICT-ONLY (notation, no fix)', 'STATEMENT'}
used = set()
out = []
missing = []
changes = collections.Counter()
for r in rows:
    sel = None
    for s in ('K:' + r['key'], ('D:' + r['declaration']) if r['channel'] == 'seal' else None,
              'PREFIX:' + r['key'].split(':')[0]):
        if s and s in dec:
            sel = s
            break
    if sel is None:
        missing.append(r['key'])
        continue
    used.add(sel)
    c, st, fx, note = dec[sel]
    c = r['class'] if c == '=' else c
    st = r['statement_level'] if st == '=' else st
    fx = r['fix'] if fx == '=' else fx
    assert c in CLASSES, c
    assert st in ('yes', 'no')
    for v in (c, st, fx, note):
        assert '\t' not in v and '\n' not in v
    # sanity: SEAL-B-ONLY rows must have A counts 0
    if c == 'SEAL-B-ONLY':
        assert r['coe_A'] in ('0',) and r['strict_A'] in ('0',), r['key']
    changes[(r['class'], c)] += 1
    out.append([r['key'], c, st, fx, note])

with open(f'{OUT}/overrides-A.tsv', 'w') as f:
    f.write('key\tclass\tstatement_level\tfix\tnote\n')
    for o in out:
        f.write('\t'.join(o) + '\n')

print('rows', len(rows), 'written', len(out))
print('missing', missing)
print('unused selectors', sorted(set(dec) - used))
for k, v in sorted(changes.items()):
    print(k, v)
