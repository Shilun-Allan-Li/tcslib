"""unsealable.py <candidate-dir>...: drop from every candidate list the definitions ruled to be
notation (user ruling of 2026-11-07: `Complexity.PolyExpr.eval` is notation, made reducible by #210),
like the reducible abbreviations the collector never lists. Records the dropped rows in
<candidate-dir>/unsealable-dropped.tsv."""
import sys
from pathlib import Path
UNSEALABLE = {'Complexity.PolyExpr.eval'}
for d in map(Path, sys.argv[1:]):
    dropped = []
    for f in sorted(d.glob('*.txt')):
        if f.name.endswith(('.uses.txt', '.eqn.txt')): continue
        keep = []
        for l in f.read_text(encoding='utf-8').split('\n'):
            if l.split('\t')[0] in UNSEALABLE:
                dropped.append(f"{f.name}\t{l}")
            else:
                keep.append(l)
        f.write_text('\n'.join(keep), encoding='utf-8')
    (d / 'unsealable-dropped.tsv').write_text('\n'.join(dropped) + '\n', encoding='utf-8')
    print(d.name, len(dropped), 'rows dropped')
