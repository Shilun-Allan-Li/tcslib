"""sealtable.py <head-A.tsv> <head-B.tsv> <base-A.tsv> <base-B.tsv>: per file and variant, head vs base seal
outcome (sealsum.py rows), with the declarations failing at head but not at base (new) and the reverse."""
import sys
def load(p):
    d = {}
    for l in open(p):
        f = l.rstrip('\n').split('\t')
        d[f[0].split('_', 1)[1]] = dict(rc=int(f[2]), err=int(f[3]), inst=f[4], eof=f[5], decls=set(x for x in f[6].split(',') if x))
    return d
hA, hB, bA, bB = map(load, sys.argv[1:5])
newall = []; passes = {'A': 0, 'B': 0}
print(f"{'file':72} {'A head':>12} {'A base':>12} {'B head':>12} {'B base':>12}  new / gone")
for m in sorted(hA):
    cells = []; notes = []
    for v, h, b in (('A', hA, bA), ('B', hB, bB)):
        x = h[m]; y = b.get(m)
        assert x['inst'] == '1' and x['eof'] == '1', (m, v)
        passes[v] += x['rc'] == 0
        cells.append('pass' if x['rc'] == 0 else f"FAIL {x['err']}e/{len(x['decls'])}d")
        cells.append('-' if y is None else ('pass' if y['rc'] == 0 else f"FAIL {y['err']}e/{len(y['decls'])}d"))
        if y is not None:
            new = sorted(x['decls'] - y['decls']); gone = sorted(y['decls'] - x['decls'])
            if new: notes.append(f'{v} NEW {new}'); newall += [(m, v, n) for n in new]
            if gone: notes.append(f'{v} gone {gone}')
        elif x['decls']: notes.append(f'{v} (new file) failing {sorted(x["decls"])}'); newall += [(m, v, n) for n in x['decls']]
    print(f"{m:72} {cells[0]:>12} {cells[1]:>12} {cells[2]:>12} {cells[3]:>12}  {'; '.join(notes)}")
print(f"head pass A {passes['A']}/{len(hA)}, B {passes['B']}/{len(hB)}; new failing declarations: {newall if newall else 0}")
