"""Extract every identifier named in rw/rwa/simp/simpa/dsimp/simp_rw/nth_rewrite/erw lists, unfold/delta
arguments and show/change terms of the added code (comments stripped). usage: tacargs.py <added.txt> <outprefix>"""
import re, sys, json
src = open(sys.argv[1], encoding='utf-8').read()
# strip comments, keep line structure
out=[]; i=0; depth=0
while i < len(src):
    if src.startswith('/-', i): depth+=1; i+=2; continue
    if src.startswith('-/', i) and depth>0: depth-=1; i+=2; continue
    if depth==0 and src.startswith('--', i):
        j=src.find('\n', i); i = len(src) if j<0 else j; continue
    out.append(src[i] if depth==0 else ('\n' if src[i]=='\n' else ' ')); i+=1
code=''.join(out)
IDENT = re.compile(r"(?<![\w.'₀-₉!?])(@?[A-Za-z_αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩ][\w'.₀-₉!?ℓ]*)")
KW = set('at with fun by from show if then else let have in match do this true false rfl _ ← ↦ ∀ ∃ Type Prop Sort λ only'.split())
def bracket(s, k):
    # s[k] == '[' ; return content and end index, nesting aware
    d=0
    for j in range(k, len(s)):
        if s[j] in '[': d+=1
        elif s[j] == ']':
            d-=1
            if d==0: return s[k+1:j], j
    return s[k+1:], len(s)
def split_top(s):
    parts=[]; d=0; cur=''
    for ch in s:
        if ch in '([{⟨': d+=1
        elif ch in ')]}⟩': d-=1
        if ch==',' and d==0: parts.append(cur); cur=''
        else: cur+=ch
    parts.append(cur); return [p.strip() for p in parts if p.strip()]
rows=[]
lineof = lambda pos: code.count('\n', 0, pos)+1
TAC = re.compile(r'\b(rw|rwa|rewrite|erw|simp_rw|nth_rewrite\s+\d+|nth_rw\s+\d+|simp|simpa|dsimp|simp_all)\b(\s+only)?\s*(\[)?')
for m in TAC.finditer(code):
    tac = m.group(1) + (m.group(2) or '')
    if not m.group(3):
        # simp/dsimp/simpa without list: record bare
        if m.group(1) in ('simp','simpa','dsimp','simp_all'):
            rows.append(dict(line=lineof(m.start()), tac=tac+' (no list)', item='', head=''))
        continue
    content, end = bracket(code, m.end()-1)
    for item in split_top(content):
        it = item.lstrip('←').strip()
        it = re.sub(r'^-\s*', '-', it)
        head = ''
        if it.startswith('show ') or it.startswith('(show'):
            head = '<show-from>'
        else:
            mm = IDENT.match(it.lstrip('(@-'))
            head = mm.group(1).lstrip('@') if mm else '<term>'
        rows.append(dict(line=lineof(m.start()), tac=tac, item=item, head=head))
for m in re.finditer(r'\b(unfold|delta)\s+([^\n]*)', code):
    rest = re.split(r'\bat\b|;|\)|<;>', m.group(2))[0]
    for name in rest.split():
        rows.append(dict(line=lineof(m.start()), tac=m.group(1), item=name, head=name))
for m in re.finditer(r'\b(show|change)\s+', code):
    # take the rest of the term up to ' from ' / ' by ' / ';' / end of line (and continuation lines are rare)
    seg = code[m.end(): code.find('\n', m.end())]
    seg = re.split(r'\bfrom\b|\bby\b|;|<;>', seg)[0]
    ids = sorted(set(x.lstrip('@') for x in IDENT.findall(seg)) - KW)
    for x in ids: rows.append(dict(line=lineof(m.start()), tac=m.group(1)+'-term', item=seg.strip()[:120], head=x))
json.dump(rows, open(sys.argv[2]+'.json','w'), ensure_ascii=False, indent=0)
heads = sorted(set(r['head'] for r in rows if r['head'] and not r['head'].startswith('<')))
open(sys.argv[2]+'-heads.txt','w').write('\n'.join(heads)+'\n')
print('rows', len(rows), 'distinct heads', len(heads))
from collections import Counter
print(Counter(r['tac'] for r in rows).most_common())
