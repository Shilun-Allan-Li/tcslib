import re, sys
KW = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\s+([^\s(:{\[]+)')
# v3 (gate 69 round 2 and gate 71, minor 1): anonymous instances are declarations too; they
# were skipped and their text absorbed into the previous chunk. Each is keyed by its statement.
ANON = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*instance(?=\s*[(:{\[]|\s*$)')
STOP = re.compile(r'^(end\b|namespace\b|section\b|/-!|open\b|variable\b|set_option\b|#|attribute\b|universe\b)')
def chunks(text):
    lines = text.split('\n'); out = []; pend = None; cur = None; depth = 0
    def close(i):
        nonlocal cur
        if cur:
            text = '\n'.join(lines[cur[2]:i]).rstrip()
            name = cur[0]
            if name is None:
                name = 'instance⟨' + stmt(text) + '⟩'
                while any(n == name for n, _, _ in out): name += "'"
            out.append((name, cur[1], text))
        cur = None
    for i, l in enumerate(lines):
        # v2 (B5b gate, minor 5): a line that starts inside a block comment or docstring is never
        # a declaration or a stop line (a docstring line "instance of ..." was counted as one).
        start_depth, j = depth, 0
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
            if depth == 0 and l.startswith('--', j): break
            j += 1
        if start_depth > 0: continue
        if l.startswith('/--'):
            close(i); pend = i; continue
        m = DECL.match(l)
        if m:
            if pend is None: close(i)
            start = pend if pend is not None else i; pend = None
            cur = (m.group(5), l.lstrip().startswith('private') or ' private ' in l.split(m.group(4))[0], start)
            continue
        m = ANON.match(l)
        if m:
            if pend is None: close(i)
            start = pend if pend is not None else i; pend = None
            cur = (None, l.lstrip().startswith('private'), start)
            continue
        if STOP.match(l):
            close(i); pend = None
    close(len(lines))
    return out
def stmt(t):
    body = t.split('-/', 1)[1] if t.startswith('/--') else t
    s = re.split(r':=', body, maxsplit=1)[0]
    return ' '.join(s.split())
a = chunks(open(sys.argv[1]).read()); b = chunks(open(sys.argv[2]).read())
allowed = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else set()
A = {n: (p, t) for n, p, t in a}; B = {n: (p, t) for n, p, t in b}
pubA = {n for n, (p, _) in A.items() if not p}; pubB = {n for n, (p, _) in B.items() if not p}
print('public before/after:', len(pubA), len(pubB), 'private before/after:', len(A) - len(pubA), len(B) - len(pubB))
print('public added:', sorted(pubB - pubA)); print('public removed:', sorted(pubA - pubB))
for n in sorted(pubA & pubB):
    ta, tb = A[n][1], B[n][1]
    if stmt(ta) != stmt(tb): print('STATEMENT CHANGED:', n)
    elif ta != tb:
        print(('authorized body change: ' if n in allowed else 'UNAUTHORIZED BODY CHANGE: ') + n)
privA = {n for n in A if A[n][0]}; privB = {n for n in B if B[n][0]}
print('private removed:', sorted(privA - privB)); print('private added:', sorted(privB - privA))
print('private changed:', sorted(n for n in privA & privB if A[n][1] != B[n][1]))
