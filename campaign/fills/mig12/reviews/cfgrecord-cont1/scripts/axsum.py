import sys, re, collections
# usage: axsum.py <probe output> <decls file>: axiom sets, admission walk, external privates / eqn lemmas
txt = open(sys.argv[1], encoding='utf-8').read()
decls = [l.split() for l in open(sys.argv[2], encoding='utf-8') if l.strip()]
flat = re.sub(r'\n\s+', ' ', txt)
flat = re.sub(r'_private\.[A-Za-z0-9_.]+?\.0\.', '', flat)
STD = {'propext', 'Classical.choice', 'Quot.sound'}
ax = {}
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat):
    ax[m.group(1)] = frozenset(a.strip() for a in m.group(2).split(','))
for m in re.finditer(r"'([^']+)' does not depend on any axioms", flat):
    ax[m.group(1)] = frozenset()
print('axiom prints parsed:', len(ax), 'of', len(decls))
miss = [n for n, _, _ in decls if f'Turing.{n}' not in ax]
print('missing:', miss)
bad = {n: sorted(s) for n, s in ax.items() if s - STD}
print('outside [propext, Classical.choice, Quot.sound] (incl. sorryAx):', bad or 'none')
hist = collections.Counter(tuple(sorted(s)) for s in ax.values())
for k, v in sorted(hist.items(), key=lambda kv: -kv[1]): print(f'  {v:4}  {list(k)}')
pub = [n for n, p, _ in decls if p == 'public']
print('publics:', len(pub))
for n in pub: print(f'  {n}: {sorted(ax.get("Turing."+n, ["?"]))}')
for m in re.finditer(r'(Turing\.\S+): direct sorryAx users in closure: (\[[^\]]*\])', flat): print('ADMISSION WALK', m.group(1), m.group(2))
ext = re.findall(r'EXT (\S+): external (\d+) \(TCSlib (\d+)\); external privates (\[[^\]]*\]); external eqn/unfold lemmas (\[[^\]]*\])', flat)
print('ext_check lines:', len(ext))
for n, e, t, pr, eq in ext:
    if pr != '[]' or eq != '[]': print('  EXT', n, 'privates', pr, 'eqn', eq)
m = re.search(r'EXTLIST total (\d+); TCSlib (\d+): (\[[^\]]*\])', flat)
print('EXTLIST total', m.group(1), 'TCSlib', m.group(2))
