"""trace_check.py <AxiomProbe.log> <base-sorries.txt> (gsw-6a-fills, new): check 4's analysis. Every TRACE `via`
name must be an admitted declaration (or a compiler auxiliary of one: a trailing `_proof_N`, `match_N`, `eq_N`,
`_sunfold`, … component is dropped) of an in-house module (Defs, Eval, Barrington, NANDForm, Combinators), by
suffix match against base-sorries.txt's source names; no via name may be a declaration of an owned module.
Prints the axiom census summary, every trace with its classification, and per owned module the in-house
admitted declarations reached; `layerNAND`, `layerNAND_gates`, `layerNAND_output` must have no trace."""
import sys, re, collections
log, bs = sys.argv[1:3]
INHOUSE = ['BranchingPrograms/Defs', 'BranchingPrograms/Eval', 'BranchingPrograms/Barrington',
           'CircuitComplexity/NANDForm', 'CircuitComplexity/FormulaArith/Combinators']
adm = collections.defaultdict(list)
for l in open(bs):
    m = re.match(r'^TCSlib/Complexity/(\S+): \d+: (.*)$', l.strip())
    if m: adm[m.group(1)] = [x.strip().replace('_root_.', '') for x in m.group(2).split(',')]
inh = [(mod, n) for mod in INHOUSE for n in adm[mod]]
own = [(mod, n) for mod in adm if mod not in INHOUSE for n in adm[mod]]
def parent(x):
    parts = x.split('.')
    while parts and re.fullmatch(r'_proof_\d+|match_\d+|eq_\d+|_sunfold|_unary|_binary|proof_\d+|eq_def|_simp_\d+', parts[-1]):
        parts.pop()
    return '.'.join(parts)
def cls(x):
    p = parent(x)
    for mod, n in own:
        if p == n or p.endswith('.' + n): return f'OWNED-ADMITTED({mod}:{n})'
    for mod, n in inh:
        if p == n or p.endswith('.' + n): return f'inhouse:{mod}:{n}'
    return 'UNEXPECTED'
cen = [l.rstrip('\n').split('\t') for l in open(log) if l.startswith('CENSUS')]
tr = [l.rstrip('\n').split('\t') for l in open(log) if l.startswith('TRACE')]
axset = collections.Counter(); bad = 0
for c in cen:
    for a in re.findall(r'[\w.]+', c[4]): axset[a] += 1
    if not set(re.findall(r'[\w.]+', c[4])) <= {'propext', 'Classical.choice', 'Quot.sound', 'sorryAx'}:
        print('AXIOM-UNEXPECTED', c); bad += 1
print(f'CENSUS constants={len(cen)} axioms={dict(axset)}')
reach = collections.defaultdict(set)
for t in tr:
    via = re.findall(r'[^\s\[\],]+', t[2][len('via '):])
    cl = [cls(v) for v in via]
    if not via or any(not c.startswith('inhouse:') for c in cl): bad += 1; print('TRACE-BAD', t[1], list(zip(via, cl)))
    mod = next(c[1] for c in cen if c[2] == t[1])
    for c in cl: reach[mod].add(c)
for m in sorted(reach): print(f'REACHED {m}: {sorted(reach[m])}')
for n in ['BoolCircuit.DAGCircuit.layerNAND', 'BoolCircuit.DAGCircuit.layerNAND_gates', 'BoolCircuit.DAGCircuit.layerNAND_output']:
    t = [x for x in tr if x[1] == n]
    print(f'G6A-F14 {n}: {"EMPTY TRACE" if not t else "TRACE " + t[0][2]}')
    if t: bad += 1
print(f'RESULT traces={len(tr)} bad={bad}')
