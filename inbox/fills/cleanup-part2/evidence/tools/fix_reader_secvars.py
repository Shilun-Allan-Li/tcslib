#!/usr/bin/env python3
"""Pass explicit section variables to the defined constant in generated `<name>_def` readers.
A definition in a section with `variable (A : T)` takes `A` as an explicit argument when `A`
occurs in its header or body; the reader's left-hand side `name args` becomes `name A args`.
python3 -I fix_reader_secvars.py <root> <file>..."""
import sys, re
root = sys.argv[1]
def split_binders(h):
    out = []; i = 0
    while i < len(h):
        c = h[i]
        if c in '({[⦃':
            close = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}[c]; d = 0; j = i
            while j < len(h):
                if h[j] == c: d += 1
                elif h[j] == close:
                    d -= 1
                    if d == 0: break
                j += 1
            out.append(h[i:j + 1]); i = j + 1
        elif c.isspace(): i += 1
        else: i += 1
    return out
for f in sys.argv[2:]:
    s = open(f'{root}/{f}').read(); lines = s.split('\n')
    # explicit section variables in scope per line
    stack = [[]]; scope = []
    for l in lines:
        t = l.strip()
        if re.match(r'^(namespace|section)\b', t): stack.append(list(stack[-1]))
        elif re.match(r'^end\b', t) and len(stack) > 1: stack.pop()
        m = re.match(r'^variable\s+(.*)$', t)
        if m:
            for b in split_binders(m.group(1)):
                if b.startswith('('):
                    stack[-1] += b[1:-1].split(':')[0].split()
        scope.append(list(stack[-1]))
    edits = []
    for m in re.finditer(r"(?:private )?theorem (\S+)_def [^\n]*:\n    (\(?)(\S+)([^\n]*) =\n", s):
        name = m.group(1); fn = m.group(3)
        if fn != name: continue
        ln = s.count('\n', 0, m.start())
        vs = scope[ln]
        if not vs: continue
        d = s.rfind(f'def {name} ', 0, m.start())
        if d < 0: continue
        blk = s[d:m.start()]
        used = [v for v in vs if re.search(r'(?<![\w.])' + re.escape(v) + r'(?![\w\'])', blk)]
        if not used: continue
        a = m.end(3)
        edits.append((a, ' ' + ' '.join(used)))
    for a, t in sorted(edits, reverse=True): s = s[:a] + t + s[a:]
    open(f'{root}/{f}', 'w').write(s)
    if edits: print(f, len(edits))
