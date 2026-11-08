#!/usr/bin/env python3
"""Parenthesise the right-hand side of generated `<name>_def` readers (`=` binds tighter than
`&&`, `||`, `∧`, …). python3 -I fix_reader_paren.py <root> <file>..."""
import sys, re
root = sys.argv[1]
for f in sys.argv[2:]:
    s = open(f'{root}/{f}').read(); edits = []
    for m in re.finditer(r"/-- The defining equation of `[^\n]*\n(?:private )?theorem (\S+)_def [^\n]*:\n    [^\n]* =\n      ", s):
        b0 = m.end(); b1 = s.index(' := rfl', b0)
        body = s[b0:b1]
        if body.startswith('(') and body.endswith(')'):
            d = 0; ok = True
            for k, ch in enumerate(body):
                d += ch == '('; d -= ch == ')'
                if d == 0 and k < len(body) - 1: ok = False; break
            if ok: continue
        edits.append((b0, b1))
    for b0, b1 in sorted(edits, reverse=True):
        s = s[:b0] + '(' + s[b0:b1] + ')' + s[b1:]
    open(f'{root}/{f}', 'w').write(s)
    if edits: print(f, len(edits))
