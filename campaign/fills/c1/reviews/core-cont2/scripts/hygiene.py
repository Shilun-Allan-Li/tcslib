import sys, re
# usage: hygiene.py <unified diff> : scan the added lines (comments stripped) for banned/flagged tokens
added = []
for l in open(sys.argv[1], encoding='utf-8'):
    if l.startswith('+') and not l.startswith('+++'): added.append(l[1:].rstrip('\n'))
code, depth = [], 0
for l in added:
    out, j = [], 0
    while j < len(l):
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
        if depth == 0 and l.startswith('--', j): break
        if depth == 0: out.append(l[j])
        j += 1
    code.append(''.join(out))
print('added lines', len(added), 'code lines', sum(1 for c in code if c.strip()))
toks = ['sorry', 'admit', 'axiom', 'unfold', 'delta', 'set_option', 'open', 'section', 'variable',
        'attribute', 'decide', 'native_decide', 'noncomputable', 'macro', 'elab', '#eval', '#print',
        'simp_all', 'aesop', 'norm_num', 'unsafe', 'implemented_by', 'extern', 'dsimp', 'change', 'show', 'rfl', 'exact?', 'apply?', 'simp?', 'decreasing_by', 'termination_by', 'Classical', 'by_contra', 'native', 'csimp', 'reducible', 'irreducible', 'local', 'instance', 'deriving', 'simpa', 'erw', 'conv', 'calc', 'gcongr', 'omega', 'Nat.rec', 'cases', 'induction', 'subst']
for t in toks:
    pat = re.compile(r'(?<![A-Za-z0-9_.\'])' + re.escape(t) + r'(?![A-Za-z0-9_\'?])')
    n = sum(len(pat.findall(c)) for c in code)
    if n: print(f'{t}: {n}')
# unrestricted simp/simpa/dsimp (not followed by only)
unres = [c.strip() for c in code if re.search(r'(?<![A-Za-z_])(simp|simpa|dsimp)(?![A-Za-z_?!])(?!\s+only)', c)]
print('unrestricted simp/simpa/dsimp:', len(unres))
for c in unres: print('   ', c[:160])
w = [len(l) for l in added]
print('max width of added lines (chars):', max(w) if w else 0, '| over 100:', sum(1 for x in w if x > 100))
