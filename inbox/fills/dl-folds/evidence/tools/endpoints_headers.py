#!/usr/bin/env python3
"""Byte comparison of the audited endpoints' headers (decls2's header extraction, whitespace
untouched otherwise) and of every theorem header of the owned NM files, base against working tree."""
import subprocess
BASE = 'd3f2290a2c66f614e8807903b89ac595086578b3'
R = '/workspace/folds'
EP = {
 'TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean': ['prfFixedScheme_cpa', 'prfFixedScheme_cca1', 'not_prfFixedScheme_cca2', 'prfFixedScheme_not_cca2'],
 'TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean': ['INDSecure.adaptive_cpa'],
 'TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean': ['_root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa', '_root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa'],
 'TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/PaddedCPA.lean': ['_root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa'],
 'TCSlib/Cryptography/Implications/PublicKey.lean': ['exists_adaptiveCPA_of_rsa', 'exists_adaptiveCPA_of_factoring'],
 'TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean': ['nmSecure_cca2_of_indSecure_cca2', 'indSecure_cca2_of_nmSecure_cca2', 'indSecure_cca2_iff_nmSecure_cca2', '*'],
 'TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation.lean': ['nmSecure_of_simNMSecure', 'simNMSecure_of_nmSecure_cpa', 'simNMSecure_cpa_iff_nmSecure_cpa', '*'],
}
import re
def headers(src):
    """Raw text of each `theorem`/`lemma`/`def` header, from its keyword line up to the top-level `:=`."""
    out = {}
    lines = src.split('\n')
    for i, l in enumerate(lines):
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure)\s+(\S+)', l)
        if not m:
            continue
        buf = []
        d = 0
        done = False
        for j in range(i, len(lines)):
            t = lines[j]
            for k, ch in enumerate(t):
                if ch in '([{⟨': d += 1
                elif ch in ')]}⟩': d -= 1
                elif d == 0 and t.startswith(':=', k):
                    buf.append(t[:k]); done = True; break
                elif d == 0 and t.startswith(' where', k) and m.group(1) == 'structure':
                    buf.append(t[:k]); done = True; break
            if done: break
            buf.append(t)
        out[m.group(2)] = '\n'.join(buf)
    return out
bad = 0
n = 0
for f, names in EP.items():
    old = subprocess.run(['git', 'show', f'{BASE}:{f}'], cwd=R, capture_output=True, text=True).stdout
    new = open(f'{R}/{f}').read()
    a, b = headers(old), headers(new)
    want = names if '*' not in names else sorted(set(a) | set(b))
    for nm in want:
        if nm == '*': continue
        n += 1
        same = nm in a and nm in b and a[nm] == b[nm]
        bad += not same
        print(f"{'IDENTICAL' if same else 'DIFFERENT'}\t{f}\t{nm}")
print(f"TOTAL {n}: DIFFERENT {bad}")
