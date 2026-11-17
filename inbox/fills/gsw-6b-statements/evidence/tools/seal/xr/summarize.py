r"""summarize.py <outdir> [<rev-label>] (gsw-6b-statements sub-agent `seal`, new): the brief's per-owner summary of
one run_checkpoint.sh output directory. Reads <outdir>/seal/seal-{A,B,coeA,coeB}.tsv (sealsum.py) and the seal records
(seals-<V>/*.json: module, source sha) and writes <outdir>/seal-summary.tsv with columns
  owner, variant, requests, verified (install / EOF sums), rc, errors, counts_ok, verdict, failing declarations,
  first error line per failing declaration, source sha256, max RSS (KiB), seconds, sorry warnings (from
  run-<V>/results.jsonl: the seal elaborates sorry'd statements, so this must equal the unsealed build's count);
verdict = PASS iff rc 0, 0 errors and counts_ok (install and EOF records both show requested = verified = requests).
Prints the table and `ALL_PASS <bool>`."""
import sys, os, json, glob
od = sys.argv[1]; revl = sys.argv[2] if len(sys.argv) > 2 else ''
rows = []; allok = True
for V, name in (('A', 'A'), ('B', 'B'), ('coeA', 'coe-A'), ('coeB', 'coe-B')):
    tsv = os.path.join(od, 'seal', f'seal-{V}.tsv')
    if not os.path.exists(tsv): continue
    rec = {}; sor = {}
    for l in open(os.path.join(od, 'seal', f'run-{V}', 'results.jsonl')):
        x = json.loads(l)
        if 'module' in x: sor[x['module']] = x['sorry']
    for p in glob.glob(os.path.join(od, 'seal', f'seals-{V}', '*.json')):
        if p.endswith('manifest.json'): continue
        r = json.load(open(p)); rec[r['label']] = r
    for l in list(open(tsv))[1:]:
        f = l.rstrip('\n').split('\t')
        label, req, rc, err, ins, eof, ok, decls, first, rss, sec = f
        r = rec[label]
        verdict = 'PASS' if rc == '0' and err == '0' and ok == '1' else 'FAIL'
        allok &= verdict == 'PASS'
        rows.append([r['module'], name, req, f'{ins};{eof}', rc, err, ok, verdict, decls or '-', first or '-', r['source_sha256'], rss, sec, sor.get(r['probe_module'], '?')])
hdr = ['owner', 'variant', 'requests', 'verified', 'rc', 'errors', 'counts_ok', 'verdict', 'failing_declarations',
       'first_error_line', 'source_sha256', 'maxrss_kb', 'seconds', 'sorry_warnings']
with open(os.path.join(od, 'seal-summary.tsv'), 'w') as f:
    if revl: f.write(f'# {revl}\n')
    f.write('\t'.join(hdr) + '\n')
    for r in rows: f.write('\t'.join(map(str, r)) + '\n')
    f.write(f'# ALL_PASS {allok}\n')
print(open(os.path.join(od, 'seal-summary.tsv')).read())
