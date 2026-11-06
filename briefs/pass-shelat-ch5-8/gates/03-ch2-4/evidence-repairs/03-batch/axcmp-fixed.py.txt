"""axcmp.py: normalize `#print axioms` outputs (one line per name) and compare HEAD with base."""
import re, sys
def load(p):
    t = open(p, encoding='utf-8').read()
    d = {}
    for m in re.finditer(r"^'(.+?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", t, flags=re.M):
        d[m.group(1)] = sorted(a.strip() for a in m.group(3).split(',')) if m.group(3) is not None else []
    return d
G = '/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch/axrun/'
head, base = load(G + 'all.out'), load(G + 'base.out')
STD = {'propext', 'Classical.choice', 'Quot.sound'}
print(f'HEAD prints: {len(head)}; base prints: {len(base)}')
print('sorryAx at HEAD:', sum('sorryAx' in v for v in head.values()), '; at base:', sum('sorryAx' in v for v in base.values()))
print('non-standard axioms other than sorryAx at HEAD:', sorted({a for v in head.values() for a in v} - STD - {'sorryAx'}))
new = sorted(set(head) - set(base)); print('new names:', len(new))
for n in new: print('  NEW', n, head[n])
ch = [n for n in base if n in head and head[n] != base[n]]
print('changed axiom sets:', len(ch))
for n in ch: print('  CHANGED', n, base[n], '->', head[n])
print('missing at HEAD:', sorted(set(base) - set(head)))
for n in ['TCSlib.Cryptography.zk_proof_of_witnessRelation', 'TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp']:
    print(n, head.get(n))
