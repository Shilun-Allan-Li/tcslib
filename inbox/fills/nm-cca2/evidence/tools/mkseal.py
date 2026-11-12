#!/usr/bin/env python3
"""Build the whole-file seals of the nm-cca2 fill from the census logs: a verbatim copy of each
changed or new file (and of the base owned file) with `attribute [local irreducible]` on every seal
candidate of its full TCSlib import closure, inserted after the first `open` of its first
namespace, so the whole file is sealed. Variant A exempts `Complexity.PolyExpr.eval` as notation;
variant B seals it too."""
import re, os, sys
F = '/workspace/fill'; L = '/workspace/payload/evidence/logs/seal'
D = 'TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/'
FILES = {
  'Readers': D + 'Indistinguishability/Readers.lean',
  'Forward': D + 'Indistinguishability/Forward.lean',
  'Decrypt': D + 'Indistinguishability/Decrypt.lean',
  'Encrypt': D + 'Indistinguishability/Encrypt.lean',
  'Owned': D + 'Indistinguishability.lean',
  'Base': 'scratch/seal/BaseOwned.lean',
}
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
        hdr = ('\n/-! Seal %s of the nm-cca2 fill: a verbatim copy of `%s`, with every seal candidate of\n'
               'its full TCSlib import closure (%d definitions%s) irreducible from here on. -/\n%s\n\n'
               % (var, path, len(names), ', `PolyExpr.eval` exempt as notation' if var == 'A'
                  else ', `PolyExpr.eval` included', attr))
        open(f'{F}/scratch/seal/Seal{var}{name}.lean', 'w').write(src[:e] + hdr + src[e:])
        print(name, var, len(names), EVAL in cands)
