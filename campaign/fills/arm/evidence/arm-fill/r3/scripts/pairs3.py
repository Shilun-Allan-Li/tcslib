"""Round-3 pair enumeration from a v3 copy-text-screen output (unmodified screen; paths as keys).

v3 labels a file by its basename when that is unique in the argument list, else by the path given;
a declaration by its short name, or by its namespace-qualified name when the short name repeats in
the file. This script maps every directed hit with an added side to an unordered pair, with
spans (header line, last line, code lines, body characters) at the screened tree, and gives each
pair its round-2 id when round 2's pairs.tsv has the same unordered key (category and the two
`path::name` ends); new pairs get ids N3-001, ... (sorted). usage:
python3 -I pairs3.py <screen.out> <population.txt> <added.txt> <tree-root> <r2-pairs.tsv> <out.tsv> [<prior-pairs3.tsv> <new-id-prefix>]
out.tsv: pid, cat, A path, A name, A lines, A code, A chars, B path, B name, B lines, B code,
B chars, hits ('A>B sh/len'; ...), maxshared, r2 (yes/no)"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore3 import decls
out, popf, added, root, r2p, dst = sys.argv[1:7]
prior = sys.argv[7] if len(sys.argv) > 7 else None  # an earlier tree's pairs3.tsv: its new ids are reused
prefix = sys.argv[8] if len(sys.argv) > 8 else 'N3'
pop = [l.strip() for l in open(popf) if l.strip()]
new = {l.strip() for l in open(added) if l.strip()}
nb = {}
for p in pop: nb[os.path.basename(p)] = nb.get(os.path.basename(p), 0) + 1
lab = {(os.path.basename(p) if nb[os.path.basename(p)] == 1 else p): p for p in pop}
spans = {}
for p in pop:
    for d in decls(open(os.path.join(root, p), encoding='utf-8').read()):
        spans[(p, d['name'])] = d
P = re.compile(r'^\s+(\S+?)::(\S+)\s+reproduces\s+(\S+?)::(\S+): (\d+)/(\d+) = (\d+)%$')
pairs = {}; directed = {'same': 0, 'internal': 0, 'lib': 0}; nhits = 0
for l in open(out, encoding='utf-8'):
    m = P.match(l.rstrip('\n'))
    if not m: continue
    nhits += 1
    fa, a, fb, b, sh, ln, pct = m.groups()
    pa, pb = lab[fa], lab[fb]
    if pa not in new and pb not in new: continue
    A, B = (pa, a), (pb, b)
    assert A in spans and B in spans, (A, B)
    assert spans[B]['chars'] == int(ln), (B, ln)
    cat = 'same' if pa == pb else ('internal' if (pa in new and pb in new) else 'lib')
    directed[cat] += 1
    key = tuple(sorted([A, B])) if cat != 'lib' else ((A, B) if pa in new else (B, A))
    pairs.setdefault((cat, key), []).append((A, B, int(sh), int(ln)))
r2 = {}
for l in open(r2p, encoding='utf-8'):
    c = l.rstrip('\n').split('\t')
    if c[0] == 'pid': continue
    r2[(c[1], (c[2], c[3]), (c[7], c[8]))] = c[0]
if prior:
    for l in open(prior, encoding='utf-8'):
        c = l.rstrip('\n').split('\t')
        if c[0] == 'pid' or c[14] == 'yes': continue
        r2[(c[1], (c[2], c[3]), (c[7], c[8]))] = c[0]
rows = []
for (cat, (A, B)), hs in pairs.items():
    rows.append((r2.get((cat, A, B)), cat, A, B, hs))
newrows = sorted([r for r in rows if r[0] is None], key=lambda r: (r[1], r[2], r[3]))
for i, r in enumerate(newrows, 1):
    rows[rows.index(r)] = (f'{prefix}-{i:03d}',) + r[1:]
order = {'same': 0, 'internal': 1, 'lib': 2}
rows.sort(key=lambda r: (order[r[1]], r[0]))
with open(dst, 'w', encoding='utf-8') as f:
    f.write('pid\tcat\tA_path\tA_name\tA_lines\tA_code\tA_chars\tB_path\tB_name\tB_lines\tB_code\tB_chars\thits\tmaxshared\tr2\n')
    for pid, cat, A, B, hs in rows:
        sa, sb = spans[A], spans[B]
        hits = '; '.join(f'{"A>B" if x == A else "B>A"} {sh}/{ln}' for x, y, sh, ln in sorted(hs, key=lambda h: h[0] != A))
        f.write(f'{pid}\t{cat}\t{A[0]}\t{A[1]}\t{sa["l0"]}-{sa["l1"]}\t{sa["code"]}\t{sa["chars"]}\t{B[0]}\t{B[1]}\t{sb["l0"]}-{sb["l1"]}\t{sb["code"]}\t{sb["chars"]}\t{hits}\t{max(h[2] for h in hs)}\t{"yes" if pid[0] in "SIL" and pid[1:].isdigit() else "no"}\n')
cnt = {}
for r in rows: cnt[r[1]] = cnt.get(r[1], 0) + 1
print(f'screen hits {nhits}; directed with an added side {directed} total {sum(directed.values())}; unordered {cnt} total {len(rows)}; '
      f'with a round-2 id {sum(1 for r in rows if r[0][0] in "SIL" and r[0][1:].isdigit())}, new at this screen {len(newrows)}')
gone = sorted(set(v for v in r2.values() if v[0] in 'SIL' and v[1:].isdigit()) - {r[0] for r in rows})
print(f'round-2 pairs absent from this screen: {len(gone)}: {" ".join(gone)}')
if prior:
    pg = sorted(set(v for v in r2.values() if not (v[0] in 'SIL' and v[1:].isdigit())) - {r[0] for r in rows})
    print(f'earlier-tree new pairs absent from this screen: {len(pg)}: {" ".join(pg)}')
