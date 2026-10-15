"""The base screen's pairs against round 2's (r2/pairs.tsv, measured at e831b5b0 on flattened copies
with the v1 screen): same pair set, and per pair the same directed hits, body sizes and code lines;
only line numbers may move (comment-only changes since, e.g. #93). usage: python3 -I r2compare.py <pairs3-base.tsv> <r2-pairs.tsv>"""
import sys
rd = lambda f: {c[0]: c for c in (l.rstrip('\n').split('\t') for l in open(f, encoding='utf-8')) if c[0] != 'pid'}
a, b = rd(sys.argv[1]), rd(sys.argv[2])
print(f'pairs: base {len(a)}, round 2 {len(b)}, common ids {len(set(a) & set(b))}')
cols = {'cat': 1, 'A path': 2, 'A name': 3, 'A code lines': 5, 'A body chars': 6, 'B path': 7, 'B name': 8, 'B code lines': 10, 'B body chars': 11, 'hits': 12, 'max shared': 13}
diff = {k: [p for p in a if p in b and a[p][i] != b[p][i]] for k, i in cols.items()}
for k, v in diff.items(): print(f'  {k}: {len(v)} differ' + (f' {v[:12]}' if v else ''))
moved = [p for p in a if p in b and (a[p][4] != b[p][4] or a[p][9] != b[p][9])]
print(f'  line spans moved (either side): {len(moved)} pairs')
