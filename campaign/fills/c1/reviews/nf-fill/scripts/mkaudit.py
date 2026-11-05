"""Build the review's audit probe: the head module with `import Lean` after its last import, the
audit tail, the kinds tail and the sorry-user command, `#print axioms` for the target and every
private, then the audit commands and the kinds of the tactic-argument identifiers (python3 -I).
usage: python3 -I mkaudit.py <head.lean> <audit tail> <kinds tail> <sorry tail> <ids> <out>"""
import re, sys
src, t1, t2, t3, idsf, out = sys.argv[1:7]
L = open(src, encoding='utf-8').read().split('\n')
last = max(i for i, l in enumerate(L) if l.startswith('import '))
L.insert(last + 1, 'import Lean')
assert L[-2] == 'end Turing' and L[-1] == '', L[-3:]
privs = [m.group(2) for l in L for m in [re.match(r'^private (theorem|def|abbrev) (\S+)', l)] if m]
assert len(privs) == 39, len(privs)
ids = [i.lstrip('←').strip() for i in open(idsf, encoding='utf-8').read().split() if i.strip() and i.strip() != '_']
text = '\n'.join(L[:-1]) + '\n'
for t in (t1, t2, t3): text += open(t, encoding='utf-8').read() + '\n'
text += '\nnamespace Turing.FinNDTM\n\n#print axioms exists_codeNDTM_accepts_linear\n'
text += ''.join(f'#print axioms {n}\n' for n in privs) + '\n'
for k in range(0, len(ids), 40):
    text += '#nf_kinds ' + ' '.join(ids[k:k + 40]) + '\n'
text += '\nend Turing.FinNDTM\n\n#nf_locals\n\n#nf_axioms_all\n\n#nf_sorry_users\n\n#nf_walk\n\n#nf_alldefs\n'
open(out, 'w', encoding='utf-8').write(text)
print('wrote', out, len(text.split('\n')), 'lines;', len(privs), 'privates;', len(ids), 'identifiers')
