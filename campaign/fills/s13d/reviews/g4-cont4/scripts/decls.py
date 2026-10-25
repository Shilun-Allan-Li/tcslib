import re, sys
# usage: decls.py <file> : print "<private?> <name> <line>" for every declaration (declfreeze's comment-aware parser)
KW = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\s+([^\s(:{\[]+)')
def decls(text):
    out = []; depth = 0
    for i, l in enumerate(text.split('\n')):
        start_depth, j = depth, 0
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
            if depth == 0 and l.startswith('--', j): break
            j += 1
        if start_depth > 0: continue
        m = DECL.match(l)
        if m:
            priv = l.lstrip().startswith('private') or ' private ' in l.split(m.group(4))[0]
            out.append((priv, m.group(5), i + 1, m.group(4)))
    return out
if __name__ == '__main__':
    for p, n, ln, k in decls(open(sys.argv[1], encoding='utf-8').read()):
        print('private' if p else 'public', k, n, ln)
