import sys, re
# hygiene over the head file's added line ranges (1-based inclusive), code vs comments
h = open(sys.argv[1]).read().split('\n')
ranges = [tuple(map(int, r.split('-'))) for r in sys.argv[2].split(',')]
added = []
for a, b in ranges:
    for i in range(a, b + 1): added.append((i, h[i - 1]))
# classify comment/docstring lines
depth = 0; code = []; comment = []
for i, l in added:
    j = 0; s = ''; incomment = depth > 0
    lc = ''
    while j < len(l):
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
        if depth == 0 and l.startswith('--', j): break
        if depth == 0: lc += l[j]
        j += 1
    if lc.strip(): code.append((i, lc))
    if incomment or '/-' in l or '--' in l: comment.append((i, l))
print('added lines:', len(added), 'code lines:', len(code), 'comment/docstring-touching lines:', len(comment))
pats = {k: re.compile(v) for k, v in {
 'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom': r'\baxiom\b', 'unfold': r'\bunfold\b', 'delta': r'\bdelta\b',
 'set_option': r'\bset_option\b', 'open': r'^\s*open\b', 'section': r'^\s*(section|namespace|end)\b', 'variable': r'^\s*variable\b',
 'attribute': r'attribute\s*\[', 'native_decide': r'native_decide', 'decide(tactic)': r'\bdecide\b', 'implemented_by/extern': r'implemented_by|extern',
 'unsafe/partial': r'\b(unsafe|partial)\b', '#cmd': r'^\s*#', 'noncomputable': r'noncomputable', 'Classical': r'Classical', 'change': r'\bchange\b',
 'show': r'\bshow\b', 'rfl': r'\brfl\b', 'conv': r'\bconv\b', 'dsimp': r'\bdsimp\b', 'simp_all': r'simp_all', 'simp(no only)': r'\bsimp\b(?! only)(?!a only)(?!_all)', 'decide := ': r'decide\s*\(', 'macro/elab/syntax': r'^\s*(macro|elab|syntax|notation)\b', 'instance': r'\binstance\b', 'deriving': r'\bderiving\b', 'public decl': r'^(theorem|lemma|def|abbrev|structure|inductive|class|instance)\b',
 'private': r'^private\b'}.items()}
for k, p in pats.items():
    hits = [(i, l.strip()) for i, l in code if p.search(l)]
    print(f'== {k}: {len(hits)}')
    for i, l in hits[:80]: print(f'  {i}: {l[:150]}')
