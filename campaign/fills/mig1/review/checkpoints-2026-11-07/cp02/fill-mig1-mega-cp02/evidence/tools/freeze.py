"""freeze.py <repo> <base rev> <file>...  [--allow-add n,..] [--allow-remove n,..]
Source/public/import/body freeze of the head working tree against the base revision.
Declaration chunking is devtools/seyoon/declfreeze.py's (v4) `chunks`, loaded verbatim; the header
of a declaration is its text before the first top-level `:=` / `where` / `|` (depth-aware over
()[]{}⟨⟩, so an `(input := x)` inside a binder is not taken as the proof delimiter), with the
docstring and comments removed and whitespace normalized."""
import re, subprocess, sys, os
args = sys.argv[1:]
def opt(name):
    if name in args:
        i = args.index(name); v = args[i+1]; del args[i:i+2]; return set(x for x in v.split(',') if x)
    return set()
allow_add = opt('--allow-add'); allow_rm = opt('--allow-remove')
repo, base, files = args[0], args[1], args[2:]
src = open(os.path.join(repo, 'devtools/seyoon/declfreeze.py'), encoding='utf-8').read()
src = src[:src.index('a = chunks(open(sys.argv[1])')]
ns = {}; exec(compile(src + '\n', 'declfreeze.py', 'exec'), ns); chunks = ns['chunks']
def strip_comments(t):
    out = []; i = 0; depth = 0
    while i < len(t):
        if t.startswith('/-', i): depth += 1; i += 2; continue
        if depth and t.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i); i = len(t) if j < 0 else j; continue
        out.append(t[i]); i += 1
    return ''.join(out)
OPEN = '([{⟨'; CLOSE = ')]}⟩'
def header(t):
    s = strip_comments(t); d = 0; i = 0
    while i < len(s):
        c = s[i]
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif d == 0:
            if s.startswith(':=', i): break
            if re.match(r'\swhere\b', s[i:i+7]): break
            if c == '\n' and re.match(r'\n\s*\|', s[i:]): break
        i += 1
    return ' '.join(s[:i].split())
def code(t): return ' '.join(strip_comments(t).split())
def imports(t): return [l.strip() for l in t.split('\n') if l.startswith('import ')]
tot = {'added': [], 'removed': [], 'hdr': [], 'vis': [], 'order': [], 'imports': [], 'defbody': [], 'thmbody': []}
for f in files:
    a_txt = subprocess.run(['git', '-C', repo, 'show', f'{base}:{f}'], capture_output=True, text=True).stdout
    b_txt = open(os.path.join(repo, f), encoding='utf-8').read()
    a = chunks(a_txt); b = chunks(b_txt)
    A = {n: (p, t) for n, p, t in a}; B = {n: (p, t) for n, p, t in b}
    pubA = [n for n, p, t in a if not p]; pubB = [n for n, p, t in b if not p]
    print(f'== {f}: public {len(pubA)} -> {len(pubB)}, private {len(a)-len(pubA)} -> {len(b)-len(pubB)}')
    for n in pubB:
        if n not in A: tot['added'].append(n); print('  public ADDED', n, '(authorized)' if n in allow_add else '(UNAUTHORIZED)')
        elif A[n][0]: tot['vis'].append(n); print('  VISIBILITY private->public', n)
    for n in pubA:
        if n not in B: tot['removed'].append(n); print('  public REMOVED', n, '(authorized)' if n in allow_rm else '(UNAUTHORIZED)')
        elif B[n][0]: tot['vis'].append(n); print('  VISIBILITY public->private', n)
    surv = [n for n in pubA if n in B and not B[n][0]]
    survB = [n for n in pubB if n in A and not A[n][0]]
    if surv != survB: tot['order'].append(f); print('  RELATIVE ORDER CHANGED among surviving publics')
    for n in surv:
        ha, hb = header(A[n][1]), header(B[n][1])
        if ha != hb: tot['hdr'].append(n); print('  HEADER CHANGED', n); print('    base:', ha[:300]); print('    head:', hb[:300])
        elif code(A[n][1]) != code(B[n][1]):
            kw = re.search(r'\b(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b', ha)
            k = kw.group(1) if kw else '?'
            if k in ('def', 'abbrev', 'structure', 'inductive', 'class', 'instance'):
                tot['defbody'].append(n); print('  DEFINITION BODY CHANGED', n)
            else:
                tot['thmbody'].append(n); print('  proof body changed', n)
    ia, ib = imports(a_txt), imports(b_txt)
    if ia != ib: tot['imports'].append(f); print('  IMPORTS: added', [i for i in ib if i not in ia], 'removed', [i for i in ia if i not in ib])
print('== SUMMARY')
ua = [n for n in tot['added'] if n not in allow_add]; ur = [n for n in tot['removed'] if n not in allow_rm]
print('public added:', len(tot['added']), 'unauthorized:', ua)
print('public removed:', len(tot['removed']), 'unauthorized:', ur)
print('header changes:', tot['hdr']); print('visibility changes:', tot['vis']); print('order changes:', tot['order'])
print('import changes in:', tot['imports']); print('public definition-body changes:', tot['defbody'])
print('public proof-body changes:', len(tot['thmbody']))
print('RESULT:', 'PASS' if not (ua or ur or tot['hdr'] or tot['vis'] or tot['order'] or tot['defbody']) else 'FAIL')
