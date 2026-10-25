import sys, re
diff = open(sys.argv[1], encoding='utf-8').read().split('\n')
added = []
ln = 0
for l in diff:
    m = re.match(r'^@@ -\d+(?:,\d+)? \+(\d+)', l)
    if m: ln = int(m.group(1)); continue
    if l.startswith('+++') or l.startswith('---'): continue
    if l.startswith('+'): added.append((ln, l[1:])); ln += 1
    elif l.startswith('-'): pass
    else: ln += 1
print('added lines', len(added))
# strip comments/docstrings: track block depth over the added text in order (approximate, by line)
depth = 0; code = []
for n, l in added:
    out = []; j = 0
    while j < len(l):
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
        if depth == 0 and l.startswith('--', j): break
        if depth == 0: out.append(l[j])
        j += 1
    s = ''.join(out)
    if s.strip(): code.append((n, s))
print('added code lines (comments stripped)', len(code))
pats = {
 'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom': r'^\s*axiom\b|\baxiom\s', 'native_decide': r'native_decide',
 'unfold': r'\bunfold\b', 'delta': r'\bdelta\b', 'change': r'\bchange\b', 'show': r'\bshow\b',
 'set_option': r'\bset_option\b', 'open': r'^\s*open\b', 'section': r'^\s*section\b', 'namespace': r'^\s*namespace\b',
 'end': r'^end\b', 'variable': r'^\s*variable\b', 'attribute': r'\battribute\b', 'decide': r'\bdecide\b',
 'rfl': r'\brfl\b', 'Decidable.decide': r'Decidable\.decide', 'macro/syntax/elab': r'^\s*(macro|syntax|elab|macro_rules)\b',
 '#cmd': r'^\s*#', 'instance': r'\binstance\b', 'deriving': r'\bderiving\b', '@[simp]': r'@\[simp', '@[': r'@\[',
 'simp_all': r'\bsimp_all\b', 'aesop': r'\baesop\b', 'omega': r'\bomega\b', 'implemented_by/extern': r'implemented_by|extern',
 'public decl (no private)': r'^(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b',
 'noncomputable': r'\bnoncomputable\b', 'Classical': r'\bClassical\b', 'runFrom': r'\brunFrom\b', 'Traj': r'\bTraj\b',
 'Round.iterate': r'Round\.iterate', 'phaseHostTM': r'phaseHostTM', 'seamCompTM': r'seamCompTM', 'lockstep': r'[Ll]ockstep',
 'MultiTapeTM.mk / ⟨ machine literal': r'MultiTapeTM\.mk|tr\s*:=', 'step_of_some': r'step_of_some',
 'Action.apply': r'Action\.apply', 'irreducible/reducible attr': r'irreducible|reducible\]',
}
for k, p in pats.items():
    hits = [(n, s) for n, s in code if re.search(p, s)]
    print(f'{k}: {len(hits)}')
    if k in ('sorry','admit','axiom','native_decide','unfold','delta','set_option','open','section','namespace','end','variable','attribute','macro/syntax/elab','#cmd','instance','deriving','@[simp]','@[','public decl (no private)','noncomputable','implemented_by/extern','irreducible/reducible attr','Classical','MultiTapeTM.mk / ⟨ machine literal','phaseHostTM','seamCompTM','Round.iterate','decide','runFrom','Traj'):
        for n, s in hits[:60]: print(f'    {n}: {s.strip()[:140]}')
