"""census6b.py <CensusDump.log> <SketchResolve.log> <sketch-tokens.tsv> <new-names.tsv> <out-deflist.txt> <final-names.tsv>
(gsw-6b-statements, sub-agent probe; new; check 6, G6A-F03). Collects the foreign TCSlib definitions that
(A) a new definition's body reads (CensusDump `USE ... V` rows), (B) a target's statement mentions (`USE ... T`
rows of the targets), (C) a target's `**Proof sketch.**` names (sketch tokens resolved by SketchResolve to a
TCSlib `def` declared in another module). Reducible abbreviations, projections and instances are listed apart
(notation, never sealed). Writes the definition list for ReaderLookup.lean and prints the (who, how, def) rows."""
import sys, collections
dump, res, toks, newn, outl, finalnames = sys.argv[1:7]
mod_of = {}
for l in open(newn):
    if l.startswith('#') or not l.strip(): continue
    n, k, m = l.rstrip('\n').split('\t'); mod_of[n] = m
targets_short = {(r.split('\t')[0], r.split('\t')[1]) for r in open(toks) if r.split('\t')[2] == 'target'}
tshort = {s for _, s in targets_short}
def is_target(full): return full.split('GSW.')[-1].split('LWE.')[-1] in tshort or full.split('.')[-1] in tshort
reads = collections.defaultdict(set); notation = collections.defaultdict(set)
for l in open(dump):
    if not l.startswith('USE'): continue
    _, who, wk, part, c, ck, red, proj, loc = l.rstrip('\n').split('\t')
    if ck not in ('def', 'inductive', 'opaque'): continue
    if proj == 'instance': continue
    tag = None
    if part == 'V' and wk == 'def': tag = 'A:body'
    elif part == 'T' and wk == 'thm' and is_target(who): tag = 'B:statement'
    if tag is None: continue
    if red == 'reducible' or proj == 'projection' or ck == 'inductive':
        notation[c].add(f'{tag}:{who.split(".")[-1]}')
    else:
        reads[c].add(f'{tag}:{who.split(".")[-1]}')
resolved = collections.defaultdict(list)
for l in open(res):
    p = l.rstrip('\n').split('\t')
    if p[0] in ('RES', 'SUF') and len(p) >= 5: resolved[p[1]].append((p[2], p[3], p[4]))
for r in open(toks):
    f, decl, kind, t = r.rstrip('\n').split('\t')
    if kind != 'target': continue
    m_decl = f.replace('/', '.')[:-5]
    for (n, k, loc) in resolved.get(t, []):
        mod = loc.split(':')[0]
        if k == 'def' and mod.startswith('TCSlib') and mod != m_decl and len(resolved[t]) == 1:
            reads[n].add(f'C:sketch:{decl}')
# (C2) a sketch cites a reader `x_suffix` of a definition `x` declared in the reader's own module
fin = collections.defaultdict(lambda: collections.defaultdict(list))
for l in open(finalnames):
    if l.startswith('#'): continue
    full, short, kind, priv, loc = l.rstrip('\n').split('\t')
    if kind in ('def', 'abbrev', 'structure', 'inductive', 'class'):
        fin[loc.split(':')[0]][short].append(full)
for r in open(toks):
    f, decl, kind, t = r.rstrip('\n').split('\t')
    if kind != 'target': continue
    m_decl = f.replace('/', '.')[:-5]
    for (n, k, loc) in resolved.get(t, []):
        mod = loc.split(':')[0]
        if k != 'thm' or not mod.startswith('TCSlib') or mod == m_decl or len(resolved[t]) != 1: continue
        last = n.split('.')[-1]; path = mod.replace('.', '/') + '.lean'
        parts = last.split('_')
        for i in range(len(parts) - 1, 0, -1):
            x = '_'.join(parts[:i])
            cands = fin[path].get(x, []) + fin[path].get(x[:1].upper() + x[1:], [])
            if cands:
                ns = n.rsplit('.', 1)[0]
                dn = next((c for c in cands if c.rsplit('.', 1)[0] == ns), cands[0])
                if dn.startswith('TCSlib.') or dn.startswith('BoolCircuit') or dn.startswith('BranchingProgram'):
                    reads[dn].add(f'C2:sketch-reader:{decl}:{last}')
                break
with open(outl, 'w') as o:
    for d in sorted(reads): o.write(d + '\n')
print('# foreign TCSlib definitions read (A body, B target statement, C target sketch)')
for d in sorted(reads):
    print(f'READ\t{d}\t{" ".join(sorted(reads[d]))}')
print('# notation (reducible abbreviations, projections, structure/inductive types): never sealed, no reader needed')
for d in sorted(notation):
    if d not in reads: print(f'NOTATION\t{d}\t{len(notation[d])} uses')
print(f'RESULT defs_read={len(reads)} notation={len([d for d in notation if d not in reads])}')
