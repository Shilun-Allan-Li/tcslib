"""Round 3's K+ declarations at the base against round 2's A4+ (r2/ledger2-decls.tsv, acknowledged):
which declarations enter or leave, and which rows change size, share, class or group.
usage: python3 -I r2decls.py <r2-ledger2-decls.tsv> <ledger3-base-decls.tsv>"""
import sys
def rd(f): return {(c[0], c[1]): c for c in (l.rstrip('\n').split('\t') for l in open(f, encoding='utf-8')) if c[0] != 'path'}
a, b = rd(sys.argv[1]), rd(sys.argv[2])
short = lambda k: k[0].replace('TCSlib/Complexity/SpaceComplexity/', '').replace('TCSlib/Complexity/', '') + '::' + k[1]
print(f'round 2 A4+: {len(a)} declarations; round 3 K+ at the base: {len(b)}')
print(f'entering ({len(set(b) - set(a))}):'); [print('  +', short(k), b[k][3], 'code lines', b[k][4], 'chars', b[k][5], 'shared', b[k][6], b[k][7]) for k in sorted(set(b) - set(a))]
print(f'leaving ({len(set(a) - set(b))}):'); [print('  -', short(k), a[k][6], a[k][7]) for k in sorted(set(a) - set(b))]
ch = [k for k in sorted(set(a) & set(b)) if a[k][3:8] != b[k][3:8]]
print(f'present in both with a changed row ({len(ch)}; columns code lines, body chars, shared, class, group):')
for k in ch: print('  ~', short(k), a[k][3:8], '->', b[k][3:8])
