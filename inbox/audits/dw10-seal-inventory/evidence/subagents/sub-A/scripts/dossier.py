"""Build per-row review dossiers for sub-A (read-only inputs; writes to OUTDIR/work)."""
import json, re, sys, os, csv
from collections import defaultdict

EV = '/home/user/dw10/sub/snap-r1'
WT = '/home/user/dw10/subA'
OUT = '/home/user/dw10/exch/inbox/audits/dw10-seal-inventory/evidence/subagents/sub-A/work'
AG = 'sub-A'
os.makedirs(OUT, exist_ok=True)

rows = []
with open(f'{EV}/review/open-items.tsv') as f:
    hdr = f.readline().rstrip('\n').split('\t')
    for line in f:
        v = line.rstrip('\n').split('\t')
        d = dict(zip(hdr, v))
        if d['agent'] == AG:
            rows.append(d)

errs = defaultdict(list)
for l in open(f'{EV}/seal-errors.jsonl'):
    d = json.loads(l)
    errs[(d['path'], d['declaration'])].append(d)

readers = json.load(open(f'{EV}/readers/readers-v4.json'))
structs = json.load(open(f'{EV}/readers/readers-structs.json'))

src_cache = {}
def src(p):
    if p not in src_cache:
        try:
            src_cache[p] = open(f'{WT}/{p}').read().split('\n')
        except Exception:
            src_cache[p] = []
    return src_cache[p]

KW = r'(?:private\s+|protected\s+|noncomputable\s+|@\[[^\]]*\]\s*)*(?:theorem|lemma|def|abbrev|instance|structure|example)\s+'

def find_decl(p, decl, near=None):
    L = src(p)
    short = decl.split('.')[-1]
    pat = re.compile(r'^\s*' + KW + r'(?:[\w.]*\.)?' + re.escape(short) + r'(?:\s|$|\{|\(|:)')
    hits = [i for i, t in enumerate(L) if pat.search(t)]
    if not hits:
        return None
    if near:
        before = [h for h in hits if h + 1 <= near]
        if before:
            return before[-1]
    return hits[0]

def header_end(L, i):
    for j in range(i, min(len(L), i + 80)):
        t = L[j]
        if j > i and re.match(r'^\s*\|', t):
            return j - 1
        if re.search(r':=\s*(by)?\s*$', t) or re.search(r':=\s*by\b', t) or re.search(r'\bwhere\s*$', t):
            return j
        if re.search(r'(^|\s):=(\s|$)', t):
            return j
    return i

def rdr(name):
    out = []
    if name in readers:
        out.append('readers: ' + ', '.join(x[0].split('.')[-1] + '@' + x[1].split('.')[-1] for x in readers[name]))
    if name in structs:
        out.append('struct fields: ' + ', '.join(structs[name]))
    return '; '.join(out)

byfile = defaultdict(list)
for r in rows:
    byfile[r['base_path']].append(r)

for p, rs in byfile.items():
    fn = p.replace('TCSlib/Cryptography/', '').replace('/', '_').replace('.lean', '') + '.txt'
    L = src(p)
    with open(f'{OUT}/{fn}', 'w') as o:
        for r in rs:
            o.write('=' * 100 + '\n')
            o.write(f"KEY {r['key']} | {r['channel']} | {r['declaration']}\n")
            o.write(f"  record: {r['record']}\n  counts sA={r['strict_A']} sB={r['strict_B']} cA={r['coe_A']} cB={r['coe_B']} scan={r['scan']}\n")
            o.write(f"  tool: {r['class']} | stmt={r['statement_level']} | {r['fix']}\n  ev: {r['evidence']}\n")
            if r['channel'] == 'seal':
                es = errs.get((p, r['declaration']), [])
                ca = [e for e in es if e['variant'] == 'coe-A']
                first_line = min([e['source_line'] for e in ca], default=None)
                di = find_decl(p, r['declaration'], first_line)
                if di is not None:
                    he = header_end(L, di)
                    o.write(f"  DECL at {di+1}, header ends {he+1}\n")
                    for k in range(di, min(he + 1, di + 25)):
                        o.write(f"    {k+1:5d}| {L[k]}\n")
                else:
                    o.write('  DECL not found\n')
                for var in ('coe-A', 'coe-B'):
                    vs = [e for e in es if e['variant'] == var]
                    if var == 'coe-B' and ca:
                        continue
                    for e in sorted(vs, key=lambda e: e['probe_line']):
                        o.write(f"  -- {var} line {e['source_line']} cascade={e['cascade']} cls={e['message_class']}\n")
                        o.write(f"     providers={e['providers']}\n     referenced={e['referenced']}\n")
                        for prov in e['providers']:
                            s = rdr(prov)
                            if s:
                                o.write(f"     [{prov}] {s}\n")
                        msg = e['message'].split('\n')
                        for m in msg[:14]:
                            o.write(f"     > {m[:220]}\n")
                        if len(msg) > 14:
                            # print goal line
                            gl = [m for m in msg if m.lstrip().startswith('⊢')]
                            for m in gl[:2]:
                                o.write(f"     >> {m[:300]}\n")
                        sl = e['source_line']
                        for k in range(max(0, sl - 4), min(len(L), sl + 2)):
                            o.write(f"    {'*' if k+1==sl else ' '}{k+1:5d}| {L[k]}\n")
            else:
                m = re.match(r'(\d+)', r['scan'])
                if m:
                    sl = int(m.group(1))
                    di = find_decl(p, r['declaration'], sl)
                    if di is not None:
                        o.write(f"  DECL at {di+1}\n    {di+1:5d}| {L[di]}\n")
                    for k in range(max(0, sl - 5), min(len(L), sl + 3)):
                        o.write(f"    {'*' if k+1==sl else ' '}{k+1:5d}| {L[k]}\n")
                    dn = r['scan'].split()[-1]
                    s = rdr(dn)
                    if s:
                        o.write(f"     [{dn}] {s}\n")
print(len(rows), 'rows,', len(byfile), 'files')
