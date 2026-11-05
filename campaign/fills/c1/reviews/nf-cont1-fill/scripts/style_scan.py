# style_scan.py <diff-U0> <head file> <base file>: admissions in added lines, widths (chars), blank runs
import re, sys
diff, head, base = sys.argv[1:4]
added = [l[1:] for l in open(diff, encoding='utf-8').read().split('\n') if l.startswith('+') and not l.startswith('+++')]
print('added lines:', len(added))
pat = re.compile(r'\b(sorry|admit|axiom|native_decide|implemented_by|unsafe|extern|set_option|ofReduceBool|reduceBool|macro|elab|syntax|opaque|partial|noncomputable|reducible|irreducible|attribute|instance|deriving|import|open|variable|Classical|termination_by|decreasing_by|local|scoped|nonrec|protected)\b|#exit|#eval|@\[')
code_hits = []
depth = 0
for i, l in enumerate(added):
    # strip comments roughly: skip docstring/comment content
    s = l; out = ''; j = 0
    while j < len(s):
        if s.startswith('/-', j): depth += 1; j += 2; continue
        if s.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
        if depth == 0 and s.startswith('--', j): break
        if depth == 0: out += s[j]
        j += 1
    if pat.search(out): code_hits.append(out.strip())
print('== code hits (comments stripped) in added lines:')
for h in code_hits: print('  ', h)
for name, f in (('head', head), ('base', base)):
    L = open(f, encoding='utf-8').read().split('\n')
    w = [(len(x), i + 1) for i, x in enumerate(L)]
    print(f'== {name}: {len(L) - (1 if L[-1] == "" else 0)} lines; widest {max(w)}; >100 chars: {[i for n, i in w if n > 100]}')
    runs = []; k = 0
    for i, x in enumerate(L):
        if x.strip() == '': k += 1
        else:
            if k >= 2: runs.append((i + 1 - k, k))
            k = 0
    print(f'   blank runs >= 2 (start line, length): {runs}')
    print('   trailing whitespace lines:', [i + 1 for i, x in enumerate(L) if x != x.rstrip()])
