import re, sys
lines = open(sys.argv[1], encoding='utf-8').read().split('\n')
# strip comments/docstrings for code checks
def code_lines(lines):
    out=[]; depth=0
    for i,l in enumerate(lines,1):
        s=''; j=0
        while j < len(l):
            if l.startswith('/-', j): depth+=1; j+=2; continue
            if l.startswith('-/', j) and depth>0: depth-=1; j+=2; continue
            if depth==0 and l.startswith('--', j): break
            if depth==0: s+=l[j]
            j+=1
        out.append((i,s))
    return out
cl = code_lines(lines)
pats = {k: re.compile(v) for k,v in {
 'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom': r'\baxiom\b', 'native_decide': r'native_decide',
 'implemented_by': r'implemented_by', 'unsafe': r'\bunsafe\b', 'extern': r'@\[extern', 'set_option': r'\bset_option\b',
 'deriving': r'\bderiving\b', 'open': r'^\s*open\b', 'section': r'^\s*section\b', 'end': r'^\s*end\b', 'variable': r'^\s*variable\b',
 'attribute': r'^\s*attribute\b', 'local instance': r'local instance', 'instance (all)': r'\binstance\b',
 'macro/notation/syntax/elab': r'^\s*(macro|notation|syntax|elab|infix|prefix|postfix|macro_rules)\b',
 '@[simp]': r'@\[[^\]]*\bsimp\b', '@[reducible]/irreducible': r'@\[[^\]]*(reducible|irreducible)', 'decide': r'\bdecide\b',
 'aesop': r'\baesop\b', 'delta': r'\bdelta\b', 'convert': r'\bconvert\b', 'unfold': r'\bunfold\b', 'show': r'\bshow\b', 'change': r'\bchange\b',
 'Classical': r'Classical', 'noncomputable': r'\bnoncomputable\b', 'opaque': r'\bopaque\b', 'partial': r'\bpartial\b', '#': r'^\s*#',
 'mutual': r'\bmutual\b', 'public decl (no private)': r'^(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b',
 'protected': r'\bprotected\b',
}.items()}
for k,p in pats.items():
    hits=[(i,s.strip()) for i,s in cl if p.search(s)]
    print(f'{k}: {len(hits)}')
    if k not in ('show','unfold','decide','Classical','end','instance (all)') or len(hits)<=40:
        for i,s in hits[:60]: print(f'   {i}: {s[:150]}')
# line widths
w=[(i,len(l)) for i,l in enumerate(lines,1) if len(l)>100]
print('lines over 100 chars:', len(w), w[:10])
# double blank lines
dbl=[i for i in range(1,len(lines)) if lines[i-1].strip()=='' and lines[i].strip()=='']
print('double blank lines:', len(dbl), dbl[:10])
# trailing whitespace
tw=[i for i,l in enumerate(lines,1) if l!=l.rstrip()]
print('trailing whitespace lines:', len(tw), tw[:10])
