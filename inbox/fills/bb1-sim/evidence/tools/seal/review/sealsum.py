# bb1-sim (lead): copied unchanged from bb1-sim-statements (exchange a3cb45f6, evidence/tools/seal/).
# bb1-sim-statements (lead): copied unchanged from the bb1-machine delivery.
"""sealsum.py <records-dir> <rundir> <touched.json> <out.tsv>: per seal probe: requests, rc, error count,
install/EOF records, and the failing declarations (error lines mapped back to source lines through the
record's source_to_probe_lines, then to declaration spans of touched.json for the source path)."""
import sys, json, re, glob, os
recdir, rd, tj, out = sys.argv[1:5]
touched = json.load(open(tj))['files']
res = {}
for l in open(os.path.join(rd, 'results.jsonl')):
    x = json.loads(l)
    if 'module' in x: res[x['module']] = x
rows = []
for p in sorted(glob.glob(os.path.join(recdir, '*.json'))):
    if p.endswith('manifest.json'): continue
    r = json.load(open(p)); m = r['probe_module']
    if m not in res: continue
    log = open(os.path.join(rd, 'mods', m.replace('/', '_') + '.log'), encoding='utf-8', errors='replace').read()
    errs = [int(x.group(1)) for x in re.finditer(r'^\S+\.lean:(\d+):\d+: error', log, re.M)]
    p2s = {d['probe_line']: d['source_line'] for d in r['source_to_probe_lines']}
    decls = touched.get(r['source'], {}).get('declarations', [])
    names = []
    for e in errs:
        s = p2s.get(e)
        d = [x['name'] for x in decls if s and x['start'] <= s <= x['end']]
        names.append(d[0] if d else f'probe:{e}/src:{s}')
    inst = 'G06-SEAL label=' + r['label'] in log; eof = 'G06-SEAL-END label=' + r['label'] in log
    rows.append((r['label'], r['requested'], res[m]['rc'], len(errs), int(inst), int(eof), sorted(set(names))))
with open(out, 'w') as f:
    for x in rows:
        f.write('\t'.join(map(str, x[:6])) + '\t' + ','.join(x[6]) + '\n')
print(len(rows), 'probes;', sum(1 for x in rows if x[2] == 0), 'pass')
