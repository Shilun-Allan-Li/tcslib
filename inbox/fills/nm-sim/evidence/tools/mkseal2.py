import re, sys
sys.path.insert(0,'/workspace/simtools')
from nmsim_files import FILES
F = '/workspace/sim'; L = '/workspace/simpay/evidence/logs/seal'
EVAL = 'Complexity.PolyExpr.eval'
for name, path in FILES.items():
    cands = [l.split()[1] for l in open(f'{L}/scan-{name}.log') if l.startswith('CAND ')]
    src = open(F + '/' + path).read()
    ns = src.index('\nnamespace ')
    m = re.compile(r'\nopen [^\n]*\n').search(src, ns)
    e = m.end()
    for var in 'AB':
        names = [c for c in cands if var == 'B' or c != EVAL]
        attr = 'attribute [local irreducible] ' + ' '.join('_root_.' + c for c in names)
        hdr = ('\n/-! Seal %s of the nm-sim fill: a verbatim copy of `%s`, with every seal candidate of\n'
               'its full TCSlib import closure (%d definitions%s) irreducible from here on. -/\n%s\n\n'
               % (var, path, len(names), ', `PolyExpr.eval` exempt as notation' if var == 'A'
                  else ', `PolyExpr.eval` included', attr))
        open(f'{F}/scratch/seal/Seal{var}{name}.lean', 'w').write(src[:e] + hdr + src[e:])
