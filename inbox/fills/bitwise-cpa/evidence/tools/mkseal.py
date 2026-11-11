# Build sealed copies of the bitwise-cpa touched code from evidence/logs/seal-scan.log.
import re, os
F = '/home/user/fill'
L = F + '/evidence/logs/seal-scan.log'
rows = [l.rstrip('\n') for l in open(L) if ' | used by ' in l and not l.startswith('INSTANCE')]
seal, regular = {}, set()
for r in rows:
    name, mod, tag, users = [x.strip() for x in r.split(' | ')]
    if not tag.startswith('regular'):
        continue
    regular.add(name)
    for u in re.findall(r'[\w.]+', users.replace('used by', '')):
        seal.setdefault(u, set()).add(name)
P = 'TCSlib/Cryptography/Encryption/PublicKey/'
files = {
  'BitwiseCPA.QueryHandler': (P + 'BitwiseCPA/QueryHandler.lean', 'SealQueryHandler'),
  'BitwiseCPA.Planted': (P + 'BitwiseCPA/Planted.lean', 'SealPlanted'),
  'BitwiseCPA.Eager': (P + 'BitwiseCPA/Eager.lean', 'SealEager'),
  'BitwiseCPA': (P + 'BitwiseCPA.lean', 'SealBitwiseCPA'),
}
os.makedirs(F + '/evidence/seal', exist_ok=True)
for short, (path, out) in files.items():
    src = open(F + '/' + path).read()
    names = sorted(seal.get(short, []))
    attr = 'attribute [local irreducible] ' + ' '.join('_root_.' + n for n in names)
    ns = src.index('\nnamespace ')
    e = src.index('\n', src.index('\nopen ', ns) + 1)
    hdr = ('\n\n/-! Seal of the bitwise-cpa fill: a verbatim copy of `%s`, with every foreign\n'
           'non-reducible TCSlib definition its touched declarations use made irreducible from the\n'
           'namespace\'s first `open` on (scan: `SealScan.lean`). -/\n%s\n' % (path, attr))
    open(F + '/evidence/seal/' + out + '.lean', 'w').write(src[:e] + hdr + src[e:])
    print(short, len(names), out)
print('regular foreign definitions:', len(regular))
open(F + '/evidence/seal/candidates.txt', 'w').write('\n'.join(sorted(regular)) + '\n')
