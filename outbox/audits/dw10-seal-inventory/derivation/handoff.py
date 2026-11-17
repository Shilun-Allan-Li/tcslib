"""handoff.py <work> <pkg> <outdir>: items.tsv of the DW-10 Complexity handoff: every recorded seal item located in
the handed-off files (pkg/list-only.txt), from the scoped input tables and the #248 ledger JSON (for the homes of
the definitions read). Writes <outdir>/items.tsv and prints per-file and per-source counts."""
import sys, csv, json, collections
work, pkg, outdir = sys.argv[1:4]
R = 'briefs/pass-shelat-ch5-8/'
LEDGER = R + 'maintainer/cleanup-incremental-2026-11-09/final-r1/11-final-read-ledger.zip:deferred-read-ledger-final-r1.json'
L = json.load(open(f'{work}/ledger/deferred-read-ledger-final-r1.json'))
cur = {o['id']: o for o in L['current_observations']}
rd = lambda f: [r for r in csv.DictReader(open(f'{pkg}/{f}'), delimiter='\t') if r['scope'] == 'HANDED-OFF']
first = lambda p: p.split(';')[0]


def reads(o):
    ch = o['channel']
    if ch == 'whole-file-seal':
        return '; '.join(sorted({f"{p['head']['spelling']} ({p['head']['home']})" for p in o.get('provider_pairs', [])
                                 if p.get('head')}))
    if ch == 'explicit-source':
        return f"{o['head']['provider']} ({o['head']['provider_home']})"
    return f"{o['provider']} ({o['provider_home']})"


rows = []
for r in rd('ledger-historical.tsv'):
    rows.append((f"H:{r['row']}", '#248 historical observation', f"historical {r['channel']}", first(r['base_path']),
                 r['canonical'], r['detail'], '-', f"#248 disposition {r['disposition_248']}",
                 f"{LEDGER} (historical_delivery.historical_rows, row {r['row']}); "
                 + R + 'fills/cleanup-part2/issued-r1/inputs/historical/cleanup-b.tsv'))
kind = {'whole-file-seal': 'seal diagnostic', 'explicit-source': 'explicit read (simp/rw/unfold)',
        'generated-equation': 'generated-equation read'}
for r in rd('ledger-current.tsv'):
    o = cur[r['id']]
    rows.append((r['id'], '#248 current observation', kind[r['channel']], first(r['base_path']), r['declaration'],
                 f"line {r['line_248']} at #248: {r['error_or_item']}", reads(o), f"#248 disposition {r['disposition_248']}",
                 f"{LEDGER} (current_observations, id {r['id']})"))
for r in rd('provider-pairs.tsv'):
    o = cur[r['id']]
    if r['set'] == 'efficiency-72':
        cons = ('cited by the efficiency fill (#285, Games/Efficiency.lean) under the 2026-11-10 provider ruling',
                R + 'fills/efficiency/issued-r1/PROOF-DEPENDENCIES.json (named_api_ledger_overlap); '
                + R + 'gates/10-efficiency/resolutions-r1.md')
    else:
        cons = ('cited by the Levin padding proof (#286, PadQuad.exists_linearTime_gStr) under the 2026-11-10 ruling',
                R + 'maintainer/proof-prerequisites-2026-11-10/provider-comparison.json (levin); '
                + R + 'maintainer/proof-prerequisites-2026-11-10/provider-ruling.md')
    rows.append((f"{'EFF72' if r['set'] == 'efficiency-72' else 'LEV52'}:{r['id']}", f"provider pair ({r['set']})",
                 'seal diagnostic (provider proof)', first(r['base_path']), r['declaration'],
                 f"failing end: {r['declaration']}; consumer end: {cons[0]}", reads(o), f"diagnostic {r['id']}",
                 cons[1] + f"; {LEDGER} (current_observations, id {r['id']})"))
for i, r in enumerate(rd('named-findings.tsv'), 1):
    rows.append((f"{r['finding']}:{i}", r['finding'], f"seal failure ({r['variant']})", r['base_path'], r['declaration'],
                 (f"{r['errors_at_record']} errors; " if r['errors_at_record'] else '') + r['note'], '-', r['finding'],
                 R + r['record'] if not r['record'].startswith('briefs/') else r['record']))
cols = ['item_id', 'source', 'kind', 'file', 'declaration', 'detail', 'reads (definition and home)', 'record_status',
        'record_path']
with open(f'{outdir}/items.tsv', 'w') as f:
    f.write('\t'.join(cols) + '\n')
    for x in rows:
        f.write('\t'.join(str(v).replace('\t', ' ').replace('\n', ' ') for v in x) + '\n')
by_file = collections.defaultdict(collections.Counter)
for x in rows:
    by_file[x[3]][x[1].split(' (')[0]] += 1
print(len(rows), collections.Counter(x[1].split(' (')[0] for x in rows))
for p in sorted(by_file):
    print(p, sum(by_file[p].values()), dict(by_file[p]))
