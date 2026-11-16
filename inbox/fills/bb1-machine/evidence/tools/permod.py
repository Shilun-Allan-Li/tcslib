r"""permod.py <logdir> <out.tsv> [seed.txt]: per-module table of a runner.py run (last record per module in
<logdir>/results.jsonl), with the error count split by form from the module log <logdir>/mods/<m>.log:
err_colon = ^\S+\.lean:\d+:\d+: error: , err_paren = ^\S+\.lean:\d+:\d+: error\( ; errors = the runner's combined count
(must equal their sum); error_substr, sorry, warnings as recorded. Checks that each log's SHA-256 equals its record.
With seed.txt, also prints the rows of those modules."""
import sys, json, re, os, hashlib
logdir, out = sys.argv[1:3]; seeds = [l.strip() for l in open(sys.argv[3])] if len(sys.argv) > 3 else []
last = {}
for l in open(os.path.join(logdir, 'results.jsonl')):
    r = json.loads(l)
    if 'module' in r: last[r['module']] = r
rows = []; bad = []
for m, r in last.items():
    lp = os.path.join(logdir, 'mods', m.replace('/', '_') + '.log'); b = open(lp, 'rb').read(); t = b.decode('utf-8', 'replace')
    if hashlib.sha256(b).hexdigest() != r['log_sha256']: bad.append(m)
    c = len(re.findall(r'^\S+\.lean:\d+:\d+: error:', t, re.M)); p = len(re.findall(r'^\S+\.lean:\d+:\d+: error\(', t, re.M))
    if c + p != r['errors']: bad.append(m)
    rows.append((m, r['rc'], c, p, r['errors'], r['error_substr'], r['sorry'], r['warnings']))
with open(out, 'w') as f:
    f.write('module\trc\terr_colon\terr_paren\terrors\terror_substr\tsorry\twarnings\n')
    for x in rows: f.write('\t'.join(map(str, x)) + '\n')
s = lambda k: sum(x[k] for x in rows)
print(f'modules {len(rows)}; rc!=0 {sum(1 for x in rows if x[1])}; error: {s(2)}; error( {s(3)}; combined {s(4)}; substring {s(5)}; '
      f'sorry {s(6)}; warnings {s(7)}; log/record mismatches {bad}')
for x in rows:
    if x[0] in seeds: print('  ' + '\t'.join(map(str, x)))
