#!/usr/bin/env python3
"""Classify the explicit-unfold scan: a resolved definition must be the scanned file's own; an
unresolved name must be the file's own private declaration or a local hypothesis."""
import re
L = '/workspace/payload/evidence/logs'
D = '/workspace/fill/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/'
files = {'Readers': D + 'Indistinguishability/Readers.lean', 'Forward': D + 'Indistinguishability/Forward.lean',
         'Decrypt': D + 'Indistinguishability/Decrypt.lean', 'Encrypt': D + 'Indistinguishability/Encrypt.lean',
         'Owned': D + 'Indistinguishability.lean'}
mods = {k: 'TCSlib.' + v.split('/TCSlib/')[1][:-5].replace('/', '.') for k, v in files.items()}
cur = None; out = []; bad = 0; counts = {}
for l in open(L + '/rwids.log'):
    l = l.rstrip('\n')
    if l.startswith('== '): cur = l[3:]; src = open(files[cur]).read(); continue
    if cur is None or ': ' not in l or l.startswith(('START', 'END')): continue
    name = l.split(':')[0]
    if 'unresolved' in l:
        if re.search(r'private (noncomputable )?def ' + re.escape(name) + r'\b', src): k = 'own private DEF'
        elif re.search(r'private theorem ' + re.escape(name) + r'\b', src): k = 'own private theorem'
        else: k = 'local hypothesis'
    elif ': DEF (' in l:
        k = 'own DEF' if l.endswith('(' + mods[cur] + ')') else 'FOREIGN DEF'
    elif ': theorem (' in l: k = 'theorem'
    else: k = 'other'
    if k == 'FOREIGN DEF' or k == 'other': bad += 1
    counts[(cur, k)] = counts.get((cur, k), 0) + 1
    out.append(f'{cur}\t{k}\t{l}')
open(L + '/rwids-classified.tsv', 'w').write('\n'.join(out) + '\n')
for (f, k), n in sorted(counts.items()): print(f'{f:8} {k:20} {n}')
print('entries', len(out), '| foreign definitions passed:', bad)
