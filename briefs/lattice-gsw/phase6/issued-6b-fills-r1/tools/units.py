"""units.py <graphdir> <outdir>: per dispatch unit of issued-6b-fills-r1, the owned modules, DOWN (every module
downstream of an owned module, owned included, root TCSlib excluded) in full import order, and ORDER (upstream
closure of DOWN) size; plus the base admissions the unit must leave (base-sorries of ORDER minus its targets)."""
import sys, json, os
gd, outd = sys.argv[1:3]
g = json.load(open(gd+'/mods.json')); imps = g['imports']
full = open(gd+'/order-full.txt').read().split(); pos = {m:i for i,m in enumerate(full)}
rev = {}
for m, xs in imps.items():
    for x in xs: rev.setdefault(x, []).append(m)
def clo(st, e):
    seen=set(); st=list(st)
    while st:
        x=st.pop()
        if x in seen: continue
        seen.add(x); st.extend(e.get(x, []))
    return seen
sor = {}
for l in open(gd+'/sorries.txt'):
    if l.startswith('TOTAL'): continue
    m, n, names = l.rstrip('\n').split(': ', 2); sor[m] = names.split(', ')
G = 'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/'
U = {'gsw-6b-u12': ['Branching'], 'gsw-6b-u13': ['DecryptFormula'], 'gsw-6b-u14-u16': ['Bootstrap', 'Leveled'],
     'gsw-6b-u15-u17': ['Circular', 'LeveledSecurity'], 'gsw-6b-u18-u19': ['PolyRatio', 'Asymptotic']}
os.makedirs(outd, exist_ok=True)
for u, fs in U.items():
    own = [G+f for f in fs]
    down = sorted({m for m in clo(own, rev) if m in pos and m != 'TCSlib'}, key=pos.get)
    order = sorted({m for m in clo(down, imps) if m in pos}, key=pos.get)
    base = sum(len(sor.get(m, [])) for m in order); mods = sum(1 for m in order if m in sor)
    tg = sum(len(sor.get(m, [])) for m in own)
    with open(f'{outd}/{u}.txt','w') as f:
        f.write(f'# {u}: OWNED {len(own)}; DOWN {len(down)}; ORDER {len(order)} modules; base admissions in ORDER {base} '
                f'declarations in {mods} modules; targets {tg}; after the fill {base-tg}\n')
        for m in own: f.write(f'OWNED\t{m}\n')
        for m in down: f.write(f'DOWN\t{m}\n')
    print(u, 'down', len(down), 'order', len(order), 'base', base, 'in', mods, 'targets', tg, 'after', base-tg)
