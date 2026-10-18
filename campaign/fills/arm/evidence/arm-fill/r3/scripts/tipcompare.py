"""The ledger at the current tip against the measured landed tree: pair keys, classes and the K+
declaration rows (sizes and classes). usage: python3 -I tipcompare.py <pairs-landed> <classify-landed>
<decls-landed> <pairs-tip> <classify-tip> <decls-tip>"""
import sys
rd = lambda f: [c for c in (l.rstrip('\n').split('\t') for l in open(f, encoding='utf-8')) if c[0] not in ('pid', 'path')]
pl, cl, dl, pt, ct, dt = [rd(f) for f in sys.argv[1:7]]
key = lambda c: (c[1], c[2], c[3], c[7], c[8])
PL = {key(c): c for c in pl}; PT = {key(c): c for c in pt}
CL = {c[0]: c for c in cl}; CT = {c[0]: c for c in ct}
only_l = [PL[k] for k in PL if k not in PT]; only_t = [PT[k] for k in PT if k not in PL]
print(f'pairs: landed {len(PL)}, tip {len(PT)}; only at landed {len(only_l)}; only at the tip {len(only_t)}')
for c in only_l: print('  only at landed:', c[0], CL[c[0]][2], CL[c[0]][4], c[2] + '::' + c[3], '~', c[7] + '::' + c[8])
for c in only_t: print('  only at the tip:', c[0], CT[c[0]][2], CT[c[0]][4], c[2] + '::' + c[3], '~', c[7] + '::' + c[8])
chg = [k for k in PL if k in PT and (PL[k][12] != PT[k][12] or CL[PL[k][0]][2:5] != CT[PT[k][0]][2:5])]
print(f'pairs at both whose hits or class/group differ: {len(chg)}')
for k in chg: print('  ', PL[k][0], PL[k][12], '->', PT[k][12], CL[PL[k][0]][2:5], '->', CT[PT[k][0]][2:5])
DL = {(c[0], c[1]): c[3:] for c in dl}; DT = {(c[0], c[1]): c[3:] for c in dt}
print(f'K+ declarations: landed {len(DL)}, tip {len(DT)}; identical rows (code lines, chars, shared, class, group, manual): {sum(1 for k in DL if DT.get(k) == DL[k])}')
for k in sorted(set(DL) ^ set(DT)): print('  in one table only:', k)
for k in sorted(k for k in DL if k in DT and DT[k] != DL[k]): print('  row differs:', k, DL[k], DT[k])
