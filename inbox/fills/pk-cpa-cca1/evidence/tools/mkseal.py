# Build sealed copies of every changed or new file of the pk-cpa-cca1 fill from seal-scan.log:
# a verbatim copy with `attribute [local irreducible]` on every regular foreign TCSlib definition
# that the file's scanned roots use, from the namespace's first `open` on (so the whole file is
# sealed). Also writes the union of candidates.
import re, os, sys
F = '/home/user/fill'
rows = [l.rstrip('\n') for l in open(F + '/evidence/logs/seal-scan.log')
        if ' | used by ' in l and not l.startswith('INSTANCE')]
seal, regular = {}, set()
for r in rows:
    name, mod, tag, users = [x.strip() for x in r.split(' | ')]
    if not tag.startswith('regular'):
        continue
    regular.add(name)
    for u in re.findall(r'[\w.]+', users.replace('used by', '')):
        seal.setdefault(u, set()).add(name)
P = 'TCSlib/Cryptography/Encryption/PrivateKey/'
files = {
  'OracleFromPRF.Games': (P + 'OracleFromPRF/Games.lean', 'SealGames'),
  'OracleFromPRF.Handler': (P + 'OracleFromPRF/Handler.lean', 'SealHandler'),
  'OracleFromPRF.Reduction': (P + 'OracleFromPRF/Reduction.lean', 'SealReduction'),
  'OracleFromPRF.Transfer': (P + 'OracleFromPRF/Transfer.lean', 'SealTransfer'),
  'OracleFromPRF.Lazy': (P + 'OracleFromPRF/Lazy.lean', 'SealLazy'),
  'OracleFromPRF.Collision': (P + 'OracleFromPRF/Collision.lean', 'SealCollision'),
  'OracleFromPRF': (P + 'OracleFromPRF.lean', 'SealOracleFromPRF'),
  'OracleSecurity': (P + 'OracleSecurity.lean', 'SealOracleSecurity'),
}
os.makedirs(F + '/evidence/seal', exist_ok=True)
for short, (path, out) in files.items():
    src = open(F + '/' + path).read()
    names = sorted(seal.get(short, []))
    attr = 'attribute [local irreducible] ' + ' '.join('_root_.' + n for n in names)
    ns = src.index('\nnamespace ')
    m = re.compile(r'\nopen [^\n]*\n').search(src, ns)
    e = m.end() if m else src.index('\n', ns + 1) + 1
    hdr = ('\n/-! Seal of the pk-cpa-cca1 fill: a verbatim copy of `%s`, with every foreign\n'
           'non-reducible TCSlib definition its scanned declarations use made irreducible from the\n'
           'namespace\'s first `open` on (scan: `SealScan.lean`). -/\n%s\n\n' % (path, attr))
    open(F + '/evidence/seal/' + out + '.lean', 'w').write(src[:e] + hdr + src[e:])
    print(short, len(names), out)
print('regular foreign definitions:', len(regular))
open(F + '/evidence/seal/candidates.txt', 'w').write('\n'.join(sorted(regular)) + '\n')
