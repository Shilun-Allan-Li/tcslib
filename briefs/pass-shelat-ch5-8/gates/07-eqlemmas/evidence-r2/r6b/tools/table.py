"""table.py <g04r4-dir>: the per-file seal table (markdown, stdout) from the final evidence logs."""
import json, re, sys
from pathlib import Path
G = Path(sys.argv[1])
files = [l.strip() for l in open(G / 'changed-files.txt') if l.strip()]
def results(name):
    r = {}
    cur = None
    for l in open(G / name, encoding='utf-8'):
        m = re.match(r'^(TCSlib/\S+\.lean): candidates=(\d+).*? (PASS|FAIL|SEAL-ERROR) \(', l)
        if m: cur = m.group(1); r[cur] = [m.group(3), int(m.group(2)), 0]; continue
        if cur and re.match(r'\s+TCSlib/\S+:\d+:\d+ ', l): r[cur][2] += 1
    return r
fin, base, plain = results('seal-evidence.log'), results('seal-control-base.log'), results('seal-plain.log')
summ = {}
for l in open(G / 'candidates' / 'summary.tsv', encoding='utf-8'):
    p = l.rstrip('\n').split('\t')
    summ[p[0]] = (int(p[1].split('=')[1]), int(p[2].split('=')[1]))
un = json.load(open(G / 'unseal.json'))
scan = {}
sec = None
for l in open(G / 'scan.log', encoding='utf-8'):
    if l.startswith('## (c1)'): sec = 1; continue
    if l.startswith('## '): sec = None; continue
    if sec and not l.startswith('#') and l.strip():
        scan[l.split(':')[0]] = scan.get(l.split(':')[0], 0) + 1
print("| # | file (`TCSlib/Cryptography/…`) | candidates (sealed + already irreducible) | seal now | named entries | plain seal now (no entry) | `$BASE` control (same entries) | scan hits |")
print("|---|---|---|---|---|---|---|---|")
for i, f in enumerate(files, 1):
    mod = f[:-5].replace('/', '.')
    n, irr = summ[mod]
    ents = un.get(f, [])
    kind = 'type-level' if '/Games/' in f else 'exclusion'
    e = f"{len(ents)} {kind}" if ents else "none"
    pl = plain.get(f, ['?', 0, 0]); b = base.get(f, ['?', 0, 0]); fi = fin.get(f, ['?', 0, 0])
    pls = pl[0] + (f" ({pl[2]} error lines)" if pl[0] != 'PASS' else '')
    bs = b[0] + (f" ({b[2]} error lines)" if b[0] != 'PASS' else '')
    print(f"| {i} | `{f.replace('TCSlib/Cryptography/', '')}` | {n - irr}" + (f" + {irr}" if irr else "") +
          f" | **{fi[0]}** | {e} | {pls} | {bs} | {scan.get(f, 0)} |")
