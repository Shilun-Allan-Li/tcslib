"""sealsum.py <records-dir> <rundir> <touched.json> <out.tsv>: per seal probe: requests, rc, error count,
install/EOF records, and the failing declarations (error lines mapped back to source lines through the
record's source_to_probe_lines, then to declaration spans of touched.json for the source path).
[gsw-6b-statements sub-agent `seal` changes: (1) the install/EOF columns are now the SUMS of `requested`/`verified`
over every `G06-SEAL label=<label>[_partN]` resp. `G06-SEAL-END ...` record of the log (chunked seals give one record
per part), written as `inst=<requested>/<verified>`, `eof=<requested>/<verified>`, plus a `counts_ok` column (1 iff
both sums equal the probe's request count and at least one record of each kind exists); (2) a header line; (3) each
failing declaration is followed by the raw log line of its first error (`decl@<log line>`) in an extra column;
(4) max RSS and seconds columns; (5) the `pass` count printed requires rc 0, 0 errors and counts_ok.]"""
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
    errl = [(int(x.group(1)), x.group(0)) for x in re.finditer(r'^\S+\.lean:(\d+):\d+: error.*$', log, re.M)]
    errs = [e for e, _ in errl]
    p2s = {d['probe_line']: d['source_line'] for d in r['source_to_probe_lines']}
    decls = touched.get(r['source'], {}).get('declarations', [])
    names, first = [], {}
    for e, txt in errl:
        s = p2s.get(e)
        d = [x['name'] for x in decls if s and x['start'] <= s <= x['end']]
        nm = d[0] if d else f'probe:{e}/src:{s}'
        names.append(nm); first.setdefault(nm, txt)
    lab = re.escape(r['label'])
    ins = [(int(a), int(b)) for a, b in re.findall(r'G06-SEAL label=' + lab + r'(?:_part\d+)? requested=(\d+) .*?verified=(\d+)', log)]
    eof = [(int(a), int(b)) for a, b in re.findall(r'G06-SEAL-END label=' + lab + r'(?:_part\d+)? requested=(\d+) verified=(\d+)', log)]
    si = (sum(a for a, _ in ins), sum(b for _, b in ins)); se = (sum(a for a, _ in eof), sum(b for _, b in eof))
    ok = int(bool(ins) and bool(eof) and si == (r['requested'],) * 2 and se == (r['requested'],) * 2)
    rows.append((r['label'], r['requested'], res[m]['rc'], len(errs), f'inst={si[0]}/{si[1]}', f'eof={se[0]}/{se[1]}', ok,
                 sorted(set(names)), ' || '.join(f'{k}@{v}' for k, v in sorted(first.items())), res[m]['maxrss_kb'], res[m]['seconds']))
with open(out, 'w') as f:
    f.write('probe\trequests\trc\terrors\tinstall\teof\tcounts_ok\tfailing_declarations\tfirst_error_lines\tmaxrss_kb\tseconds\n')
    for x in rows:
        f.write('\t'.join(map(str, x[:7])) + '\t' + ','.join(x[7]) + '\t' + x[8] + '\t' + '\t'.join(map(str, x[9:])) + '\n')
print(len(rows), 'probes;', sum(1 for x in rows if x[2] == 0 and x[3] == 0 and x[6] == 1), 'pass')
