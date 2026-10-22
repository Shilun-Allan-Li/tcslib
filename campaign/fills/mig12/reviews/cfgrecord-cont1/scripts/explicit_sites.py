import re, sys, collections
# usage: explicit_sites.py <base> <head> <defs...>: per declaration, the number of times each definition
# (short name without the `Turing.` prefix) is named as a whole identifier inside a simp/rw/unfold/...
# argument list or after `unfold`/`delta`, in comment-stripped code; base vs head.
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)')
TAC = re.compile(r'\b(rw|rwa|erw|simp only|simp|simpa only|simpa|norm_num|dsimp only|dsimp|simp_rw|field_simp|simp_all)\s*\[([^\]]*)\]', re.S)
UNF = re.compile(r'\b(unfold|delta)\s+([A-Za-z_][\w.\']*(?:[ \t]+[A-Za-z_][\w.\']*)*)')
def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        out.append(src[i] if depth == 0 or src[i] == '\n' else ' ')
        i += 1
    return '\n'.join(l.split('--')[0] for l in ''.join(out).split('\n'))
def sites(path, defs):
    code = strip(open(path, encoding='utf-8').read()); lines = code.split('\n')
    starts = [(i, DECL.match(l).group(5)) for i, l in enumerate(lines) if DECL.match(l)]
    def decl_at(off):
        ln = code.count('\n', 0, off); name = '?'
        for i, n in starts:
            if i <= ln: name = n
            else: break
        return name
    c = collections.Counter()
    for m in TAC.finditer(code):
        for a in m.group(2).split(','):
            a = re.sub(r'^\s*←\s*', '', a).strip().split()
            if a and a[0] in defs: c[(decl_at(m.start()), a[0])] += 1
    for m in UNF.finditer(code):
        for a in m.group(2).split():
            if a in defs: c[(decl_at(m.start()), a)] += 1
    return c
defs = {d.replace('Turing.', '') for d in sys.argv[3:]}
A, B = sites(sys.argv[1], defs), sites(sys.argv[2], defs)
print('explicit named sites: base', sum(A.values()), 'head', sum(B.values()))
for k in sorted(set(A) | set(B)):
    if A[k] != B[k]: print(f'  {k[0]:40} {k[1]:28} base {A[k]} head {B[k]}')
bd = collections.Counter(); hd = collections.Counter()
for (n, d), v in A.items(): bd[d] += v
for (n, d), v in B.items(): hd[d] += v
print('by definition (base -> head):', {d: (bd[d], hd[d]) for d in sorted(set(bd) | set(hd))})
