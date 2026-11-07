"""mkcollect.py <seal-dir> <out.lean> <module:file-stem>...: the collector probe over the touched
declarations of each changed module (touched-<stem>.txt)."""
import sys, os
sd, out = sys.argv[1], sys.argv[2]
pairs = [a.split(':') for a in sys.argv[3:]]
imports = ['TCSlib.Cryptography.Candidates.Rabin', 'TCSlib.Cryptography.Candidates.DiscreteLogHardcore',
           'TCSlib.Cryptography.Candidates.ElGamal', 'TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas',
           'TCSlib.Cryptography.Asymptotic.PublicKeyLemmas']
body = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'collect_body.lean')).read()
lines = [f'import {m}' for m in imports] + [body]
for mod, stem in pairs:
    names = [l.strip() for l in open(os.path.join(sd, f'touched-{stem}.txt')) if l.strip()]
    lst = ', '.join('"' + n.replace('\\', '\\\\') + '"' for n in names)
    lines.append(f'#collect {mod} [{lst}]')
    lines.append(f'#axs {mod} [{lst}]')
open(out, 'w').write('\n'.join(lines) + '\n')
