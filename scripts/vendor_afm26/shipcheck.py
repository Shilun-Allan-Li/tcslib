import sys, re
# usage: shipcheck.py <worktree> <vendor-map.tsv> <out file>: concatenate the shipped files (Compat first,
# then the map's dependency order), dropping imports of TCSlib.Programs modules, for one read-only elaboration.
wt, mapf, out = sys.argv[1], sys.argv[2], sys.argv[3]
rels = ['TCSlib/Programs/Compat.lean'] + [l.split('\t')[1] for l in open(mapf) if l.strip()]
mods = {r[:-5].replace('/', '.') for r in rels}
imps, parts = [], []
for r in rels:
    t = open(f'{wt}/{r}', encoding='utf-8').read(); body = []
    for l in t.split('\n'):
        mi = re.match(r'^import (\S+)\s*$', l)
        if mi:
            d = mi.group(1)
            if d in mods: continue
            assert d.startswith('Mathlib'), (r, d)
            if d not in imps: imps.append(d)
            continue
        body.append(l)
    tag = 'Ship_' + r[:-5].replace('/', '_')
    parts.append(f'\n-- ===== {r} =====\nsection {tag}\n' + '\n'.join(body) + f'\nend {tag}\n')
open(out, 'w', encoding='utf-8').write('import Lean.Util.FoldConsts\n' + '\n'.join(f'import {i}' for i in imps) + '\n' + ''.join(parts) + '''
open Lean Elab Command in
elab "#file_census" : command => do
  let env ← getEnv
  let mut n := 0
  let mut sorried : Array Name := #[]
  let mut axs : Array Name := #[]
  for (c, ci) in env.constants.map₂.toList do
    n := n + 1
    if ci.getUsedConstantsAsSet.contains ``sorryAx then sorried := sorried.push c
    if ci matches .axiomInfo _ then axs := axs.push c
  logInfo m!"constants declared here: {n}; direct sorryAx users: {sorried}; axioms declared: {axs}"
#file_census
#print axioms Light.Compiler.compileProgram_correct
#print axioms Light.sort_meets
''')
print(len(rels), 'files')
