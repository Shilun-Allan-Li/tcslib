"""Check that required definitions are sealed in every seal log given (python3 -I).
Usage: seal_coverage.py <log> [...]  Prints, per log, the status of each required name."""
import json, re, sys
REQ = ['TCSlib.Cryptography.Encryption.PublicKey.Regev.augmented', 'TCSlib.Cryptography.LWE.sample',
       'TCSlib.Cryptography.Hashing.SIS.hash', 'TCSlib.Cryptography.Hashing.SIS.hashColumns',
       'TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.encrypt',
       'TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.lift',
       'TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.gadget',
       'TCSlib.Cryptography.distAdv', 'TCSlib.Cryptography.acceptProb',
       'TCSlib.Cryptography.Encryption.PublicKey.Regev.hashParameters',
       'TCSlib.Cryptography.LWE.decisionAdvantage',
       'TCSlib.Cryptography.Encryption.PublicKey.Regev.extractionError']
ok = True
for log in sys.argv[1:]:
    rows = {}
    for m in re.finditer(r'GSWSEC-CATALOG \S+ (\{.*\})$', open(log).read(), re.M):
        r = json.loads(m[1]); rows[r['name']] = r
    st = []
    for n in REQ:
        r = rows.get(n)
        s = 'absent' if r is None else ('SEALED' if r['eligible'] else 'not-sealed')
        ok &= s != 'not-sealed'
        st.append(f'{n.rsplit(".", 1)[-1]}={s}')
    print(f'{log.rsplit("/", 1)[-1]}: ' + ' '.join(st))
print('SEAL COVERAGE ' + ('PASS' if ok else 'FAIL'))
