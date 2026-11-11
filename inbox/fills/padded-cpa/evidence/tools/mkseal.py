# Build sealed copies of the padded-cpa touched code from evidence/logs/seal-scan.log.
import re, os, sys
F = '/home/user/fill'
L = F + '/evidence/logs/seal-scan.log'
rows = [l.rstrip('\n') for l in open(L) if ' | used by ' in l and not l.startswith('INSTANCE')]
seal = {}
regular = set()
for r in rows:
    name, mod, tag, users = [x.strip() for x in r.split(' | ')]
    if not tag.startswith('regular'):
        continue
    regular.add(name)
    for u in re.findall(r'[\w.]+', users.replace('used by', '')):
        seal.setdefault(u, set()).add(name)
P = 'TCSlib/Cryptography/Encryption/PublicKey/'
files = {
  'OracleSecurity.ChallengeSim': (P + 'OracleSecurity/ChallengeSim.lean', 'SealChallengeSim', None),
  'OracleSecurity.RecordHandler': (P + 'OracleSecurity/RecordHandler.lean', 'SealRecordHandler', None),
  'OracleSecurity': (P + 'OracleSecurity.lean', 'SealOracleSecurity', '\nopen ChallengeSim ProbComp\n'),
}
os.makedirs(F + '/evidence/seal', exist_ok=True)
for short, (path, out, anchor) in files.items():
    src = open(F + '/' + path).read()
    names = sorted(seal.get(short, []))
    attr = 'attribute [local irreducible] ' + ' '.join('_root_.' + n for n in names)
    if anchor is None:  # whole file: after the first `open` line following the namespace
        ns = src.index('\nnamespace ')
        e = src.index('\n', src.index('\nopen ', ns) + 1)
        what = 'a verbatim copy of `%s`' % path
    else:               # touched section only: after its `open` line
        e = src.index(anchor) + len(anchor) - 1
        what = 'a verbatim copy of `%s`, sealed from its touched section on' % path
    hdr = ('\n\n/-! Seal of the padded-cpa fill: %s, with every foreign non-reducible TCSlib\n'
           'definition its touched declarations use made irreducible (scan: `SealScan.lean`). -/\n%s\n'
           % (what, attr))
    open(F + '/evidence/seal/' + out + '.lean', 'w').write(src[:e] + hdr + src[e:])
    print(short, len(names), out)
print('regular foreign definitions:', len(regular))
open(F + '/evidence/seal/candidates.txt', 'w').write('\n'.join(sorted(regular)) + '\n')
