# report_tables.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Computes the REPORT.md tables from inventory.tsv and
# the evidence tables (seals.tsv, seal-decls.tsv, controls.tsv, scan.tsv): totals, status by source, class by tier, the
# named-finding counts, the Stage 2 fix list by file, the provider-reader list by provider file, the separate-ruling lists,
# the strict-only diagnostics, the HANDED-OFF counts and the NEW failures by file. Prints Markdown.
# Usage: python3 -I report_tables.py <delivery-dir>
import sys, os, csv, collections, json
dl = sys.argv[1]; ev = os.path.join(dl, 'evidence')
def tsv(p): return list(csv.DictReader(open(p, encoding='utf-8'), delimiter='\t')) if os.path.exists(p) else []
inv = tsv(os.path.join(dl, 'inventory.tsv')); seals = tsv(os.path.join(ev, 'seals.tsv')); sd = tsv(os.path.join(ev, 'seal-decls.tsv'))
ctl = tsv(os.path.join(ev, 'controls.tsv')); scan = tsv(os.path.join(ev, 'scan.tsv'))
out = []
P = out.append
def table(h, rows):
    P('| ' + ' | '.join(h) + ' |'); P('|' + '---|' * len(h))
    for r in rows: P('| ' + ' | '.join(str(x) for x in r) + ' |')
    P('')
V = ['strict-A', 'strict-B', 'coe-A', 'coe-B']
ran = [r for r in seals if r['rc'] != 'NOT_RUN']
owners = {r['path'] for r in ran}
P('### Seals'); P('')
P(f"Owners sealed (all four variants recorded): {len({r['path'] for r in seals if r['rc'] != 'NOT_RUN'} - {r['path'] for r in seals if r['rc'] == 'NOT_RUN'})} of 434. "
  f"Probes: {len(seals)} owner-variants, {sum(1 for r in ran if r['dedup_with'] == '-')} run, {sum(1 for r in ran if r['dedup_with'] != '-')} deduplicated (identical probe bytes, or identical after the SealA_/SealB_ label normalization).")
P('')
rows = []
for v in V:
    rr = [r for r in ran if r['variant'] == v]
    req = [int(r['requests']) for r in rr]
    fd = [r for r in sd if r['variant'] == v]
    tiers = collections.Counter(r['tier'] for r in fd)
    errs = sum(int(r['errors']) for r in rr)
    rows.append([v, len(rr), sum(req), max(req) if req else 0, sum(1 for r in rr if r['errors'] != '0'), len(fd), errs,
                 f"T1 {tiers.get('T1', 0)} / T2 {tiers.get('T2', 0)}", sum(1 for r in rr if not r['install'].startswith('ok') or not r['eof'].startswith('ok'))])
table(['variant', 'owners', 'requests (sum)', 'requests (max)', 'failing owners', 'failing declarations', 'errors', 'failing decls by tier', 'install/EOF incomplete'], rows)
if ctl:
    P('### Controls'); P('')
    c = collections.Counter(r['status'] for r in ctl)
    P(f"Owners: {len(ctl)}; pairs {c.get('pair', 0)}; negative only (`no reader`) {c.get('no reader', 0)}; defines nothing {c.get('defines nothing', 0)}; "
      f"no passing candidate {c.get('no passing candidate', 0)}.")
    P('')
if scan:
    P('### Explicit-unfold scan'); P('')
    f = [r for r in scan if r['foreign'] == 'yes']
    t = collections.Counter(r.get('tier', '?') for r in f)
    P(f"Items: {len(scan)}; foreign TCSlib definition items {len(f)} (T1 {t.get('T1', 0)}, T2 {t.get('T2', 0)}); by kind: " + ', '.join(f'{k} {v}' for k, v in collections.Counter(r['kind'] for r in scan).most_common()))
    P('')
P('### Status by source'); P('')
srcs = ['#248-historical', '#248-current', 'provider-pair', 'SG-F07', 'SY-F07', 'C-F02', 'new']
sts = ['HANDED-OFF', 'FIXED_SINCE', 'STILL_OPEN', 'CHANGED', 'NEW', 'NOT_CHECKED']
c = collections.Counter((r['source'], r['status']) for r in inv)
table(['source'] + sts + ['total'], [[s] + [c.get((s, t), 0) for t in sts] + [sum(c.get((s, t), 0) for t in sts)] for s in srcs] +
      [['total'] + [sum(c.get((s, t), 0) for s in srcs) for t in sts] + [len(inv)]])
P('### Class by tier (open items)'); P('')
cls = ['STAGE2', 'STAGE2-PROVIDER-READER', 'SEAL-B-ONLY', 'STRICT-ONLY (notation, no fix)', 'STATEMENT']
c = collections.Counter((r['tier'], r['class']) for r in inv if r['class'] != '-')
table(['tier'] + cls, [[t] + [c.get((t, k), 0) for k in cls] for t in ('T1', 'T2')])
P('### Named findings against their records'); P('')
rows = []
for f in ('SG-F07', 'SY-F07', 'C-F02'):
    rr = [r for r in inv if r['source'] == f]
    st = collections.Counter(r['status'] for r in rr)
    rows.append([f, len(rr), ', '.join(f'{k} {v}' for k, v in sorted(st.items()))])
table(['finding', 'rows', 'statuses'], rows)
def bypath(rows): 
    d = collections.OrderedDict()
    for r in sorted(rows, key=lambda r: (r['base_path'], r['declaration'])): d.setdefault(r['base_path'], []).append(r)
    return d
P('### Stage 2 fix list, by file'); P('')
st2 = [r for r in inv if r['class'] == 'STAGE2']
for p, rr in bypath(st2).items():
    P(f'**{p}** ({len(rr)} items)'); P('')
    table(['item', 'declaration', 'read', 'fix', 'pending'], [[r['item_id'], f"`{r['declaration']}`", (r['scan'] if r['scan'] != '-' else r['record'])[:90], r['fix'], r['pending']] for r in rr])
P('Totals per file: ' + '; '.join(f'{p.split("TCSlib/")[-1]} {len(rr)}' for p, rr in bypath(st2).items()) + f' (total {len(st2)}).')
P('')
P('### Provider-reader list (STAGE2-PROVIDER-READER), by provider file'); P('')
pr = [r for r in inv if r['class'] == 'STAGE2-PROVIDER-READER']
byp = collections.OrderedDict()
for r in sorted(pr, key=lambda r: r['fix']):
    prov = r['fix'].split(':', 1)[0].replace('provider ', '')
    byp.setdefault(prov, []).append(r)
for p, rr in byp.items():
    P(f'**{p}**'); P('')
    table(['reader needed', 'owner items'], [[k, ', '.join(sorted({x["item_id"] for x in v}))] for k, v in
          collections.OrderedDict((r['fix'].split(': ', 1)[1].split(';')[0], [x for x in rr if x['fix'].split(': ', 1)[1].split(';')[0] == r['fix'].split(': ', 1)[1].split(';')[0]]) for r in rr).items()])
for k in ('SEAL-B-ONLY', 'STATEMENT'):
    P(f'### For separate ruling: {k}'); P('')
    rr = [r for r in inv if r['class'] == k]
    table(['file', 'items', 'declarations'], [[p.split('TCSlib/')[-1], len(v), ', '.join(sorted({f"`{x['declaration']}`" for x in v}))[:400]] for p, v in bypath(rr).items()])
P('### STRICT-ONLY (notation, no fix): recorded diagnostics only (Q3)'); P('')
rr = [r for r in inv if r['class'].startswith('STRICT-ONLY')]
table(['file', 'items', 'strict errors (A+B)'], [[p.split('TCSlib/')[-1], len(v), sum(int(x['strict_A']) + int(x['strict_B']) for x in v if x['strict_A'] not in ('-', ''))] for p, v in bypath(rr).items()])
P('### HANDED-OFF'); P('')
ho = [r for r in inv if r['status'] == 'HANDED-OFF']
c = collections.Counter(r['source'] for r in ho)
P('By source: ' + ', '.join(f'{k} {v}' for k, v in c.items()) + f' (total {len(ho)}).'); P('')
table(['file', 'items'], [[p.split('TCSlib/')[-1], len(v)] for p, v in bypath(ho).items()])
P('### NEW failures, by file'); P('')
nw = [r for r in inv if r['status'] == 'NEW']
table(['file', 'seal', 'unfold', 'eqn', 'attribution', 'classes'], [[p.split('TCSlib/')[-1], sum(x['channel'] == 'seal' for x in v), sum(x['channel'] == 'unfold' for x in v),
       sum(x['channel'] == 'eqn' for x in v), ', '.join(sorted({x['known_record'] for x in v})), ', '.join(f'{k} {n}' for k, n in collections.Counter(x['class'] for x in v).items())] for p, v in bypath(nw).items()])
print('\n'.join(out))
