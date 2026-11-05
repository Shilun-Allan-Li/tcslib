"""Gate 91 round 2's resolution (minor 1): the chain's module order.
Usage: python3 -I chain_order.py <worktree>
Prints, in dependency order, every module that is (a) one of the 16 Codec modules, or (b) in the
upstream import closure of a Codec module and downstream of (or equal to) Machines/ARMProof, the one
file in which #182's head 94093275 differs from the replayed 8fd6f91a (oleans-larm)."""
import os, re, sys
wt = sys.argv[1]; P = 'TCSlib.Complexity.SpaceComplexity.'
def imps(m):
    f = os.path.join(wt, m.replace('.', '/') + '.lean')
    return [x for x in re.findall(r'^import\s+(\S+)', open(f).read(), re.M) if x.startswith('TCSlib')] if os.path.exists(f) else []
codec = [P + 'Codec.' + m for m in 'Word Scan Valid Step Langs Checks Bridge Engine Regs Machine Run Parse Layout Deciders Layout2 StepDecider'.split()]
up = set(); st = list(codec)
while st:
    x = st.pop()
    for y in imps(x):
        if y not in up: up.add(y); st.append(y)
memo = {}
def reaches(m):  # m imports ARMProof transitively, or is it
    if m == P + 'Machines.ARMProof': return True
    if m not in memo: memo[m] = False; memo[m] = any(reaches(y) for y in imps(m))
    return memo[m]
need = set(codec) | {m for m in up if reaches(m)}
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for y in imps(m):
        if y in need: visit(y)
    order.append(m)
for m in sorted(need): visit(m)
print('\n'.join(order))
