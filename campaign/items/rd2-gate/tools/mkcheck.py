"""Write #check probes (chunks of at most 80 lines): the harness text followed by one
`#check @cand` line per candidate qualification of each cited token.
Writes OUTPREFIX_<k>.lean and MAP (file, line, token, candidate)."""
import sys
harness, cited, outprefix, mapf = sys.argv[1:5]
skip = {'i.val', 'x.length', 'Finset.univ.toList', 'TCSlib.Complexity.FormulaKit.Emit',
        'TCSlib.Complexity.FormulaKit.Gate', 'FormulaKit.Gate', 'FormulaKit.Emit',
        'Complexity.QBF.truth_exSuffix_of_pointwise', 'Complexity.QBF.PrefixTruth'}
roots = ('Complexity.', 'Turing.', 'Std.', 'List.', 'Nat.', 'Finset.', 'Fintype.')
pref = ['', 'Complexity.', 'Complexity.FormulaKit.', 'Complexity.ConfigCodec.',
        'Complexity.ConfigCodec.Port.', 'Turing.', 'Std.Sat.CNF.']
def cands(t):
    if t.startswith(roots): return [t]
    if t.startswith('ConfigCodec.'): return ['Complexity.' + t]
    if t.startswith(('PolyTimeComputable.',)): return ['Complexity.' + t]
    return [p + t for p in pref]
toks = [l.split('\t')[0] for l in open(cited, encoding='utf-8').read().splitlines() if l]
h = open(harness, encoding='utf-8').read().rstrip('\n') + '\n\n-- ===== names probe =====\n'
base = len(h.split('\n'))
items = [(t, c) for t in toks if t not in skip for c in cands(t)]
mp = open(mapf, 'w', encoding='utf-8')
for k in range(0, len(items), 80):
    chunk = items[k:k + 80]
    fn = f'{outprefix}_{k // 80}.lean'
    open(fn, 'w', encoding='utf-8').write(h + '\n'.join(f'#check @{c}' for _, c in chunk) + '\n')
    for j, (t, c) in enumerate(chunk):
        mp.write(f'{fn}\t{base + j}\t{t}\t{c}\n')
print(len(items), 'candidates')
