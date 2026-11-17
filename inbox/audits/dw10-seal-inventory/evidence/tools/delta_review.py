# delta_review.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. The lead's review of the open items the seals added after
# the sub-agents' snapshot (rows of review/open-items.tsv with no reviewer). SEAL-B-ONLY / STRICT-ONLY rows are confirmed when the
# counts agree (A = 0, resp. coe = 0) and the first error (coe-B, resp. strict) names PolyExpr.eval / the FinDist coercion, or a
# definition of the same file that fails earlier under that variant (a cascade); every other row is printed for the lead to
# review by hand (manual rows in review/delta-manual.tsv, same columns, are merged in).
# Usage: python3 -I delta_review.py <evidence> <out overrides-lead-delta.tsv>
import sys, os, csv, json, collections
ev, outp = sys.argv[1:3]
rows = [r for r in csv.DictReader(open(os.path.join(ev, 'review/open-items.tsv'), encoding='utf-8'), delimiter='\t') if r['reviewed_by'] in ('-', 'lead-delta')]
E = collections.defaultdict(list)
for l in open(os.path.join(ev, 'seal-errors.jsonl'), encoding='utf-8'):
    e = json.loads(l); E[(e['path'], e['variant'])].append(e)
manual = {}
mp = os.path.join(ev, 'review/delta-manual.tsv')
if os.path.exists(mp):
    for r in csv.DictReader(open(mp, encoding='utf-8'), delimiter='\t'): manual[r['key']] = r
out, todo = [], []
COE = 'FinDist.instCoeFunForallReal'
for r in rows:
    if r['key'] in manual: m = manual[r['key']]; out.append([r['key'], m['class'], m['statement_level'], m['fix'], m['note']]); continue
    ok = None
    if r['class'] == 'SEAL-B-ONLY' and r['coe_A'] == '0' and r['strict_A'] == '0':
        es = sorted(E[(r['base_path'], 'coe-B')], key=lambda e: e['source_line'] or 0)
        mine = [e for e in es if e['declaration'] == r['declaration']]
        if mine:
            f = mine[0]
            if 'PolyExpr.eval' in f['message'] or 'Complexity.PolyExpr.eval' in f['providers']: ok = f'first coe-B error l.{f["source_line"]} reads PolyExpr.eval'
            else:
                ear = [e for e in es if (e['source_line'] or 0) < (f['source_line'] or 0) and e['declaration'] != r['declaration'] and r['declaration'].split('.')[-1] != e['declaration'].split('.')[-1]
                       and e['declaration'].split('.')[-1] in f['message']]
                if ear: ok = f'cascade: names {ear[0]["declaration"].split(".")[-1]}, which fails earlier under seal B (l.{ear[0]["source_line"]})'
                elif any('PolyExpr.eval' in e['message'] for e in es if (e['source_line'] or 0) < (f['source_line'] or 0)): ok = f'first coe-B error l.{f["source_line"]} follows an earlier PolyExpr.eval failure in the file'
    elif r['class'].startswith('STRICT-ONLY') and r['coe_A'] == '0' and r['coe_B'] == '0':
        es = [e for e in E[(r['base_path'], 'strict-A')] + E[(r['base_path'], 'strict-B')] if e['declaration'] == r['declaration']]
        if es and any(COE in p for e in es for p in e['providers'] + e['referenced']): ok = 'the strict failure is at the FinDist coercion'
        elif es and any('CoeFun.coe' in e['message'] for e in es): ok = 'the strict failure is at the FinDist coercion (`CoeFun.coe p a` against `p.prob a` in the message)'
        elif es:
            fs = [e for e in E[(r['base_path'], 'strict-A')] if (e['source_line'] or 0) < (min(x['source_line'] or 0 for x in es)) and 'CoeFun.coe' in e['message']]
            if fs: ok = f'strict-only, after the FinDist coercion failures earlier in the file (l.{fs[0]["source_line"]}); the coe variants pass'
    if ok: out.append([r['key'], r['class'], r['statement_level'], r['fix'], 'lead-delta: confirmed (' + ok + ')'])
    else: todo.append(r)
with open(outp, 'w', encoding='utf-8') as f:
    f.write('key\tclass\tstatement_level\tfix\tnote\n')
    for x in out: f.write('\t'.join(str(v).replace('\t', ' ').replace('\n', ' ') for v in x) + '\n')
print('delta rows', len(rows), 'written', len(out), 'need manual review', len(todo))
for r in todo: print('TODO', r['key'], r['class'], r['coe_A'], r['strict_A'], r['coe_B'], r['strict_B'], sep='\t')
