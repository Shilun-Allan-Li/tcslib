#!/usr/bin/env python3
"""Add the definition's result type as an ascription to generated `<name>_def` readers whose
right-hand side starts with `fun` (so that the lambda's binder types are known).
python3 -I fix_reader_lambda.py <root> <file>..."""
import sys, re
root = sys.argv[1]
for f in sys.argv[2:]:
    s = open(f'{root}/{f}').read()
    out = []; pos = 0; changed = 0
    for m in re.finditer(r"/-- The defining equation of `[^`]+`[^\n]*(?:\n(?!theorem)[^\n]*)*\n((?:private )?theorem (\S+)_def ([^\n]*):\n    (\S+)[^\n]*=\n      fun )", s):
        name = m.group(2)
        # locate the def header of `name` above this reader
        d = s.rfind(f'def {name} ', 0, m.start())
        if d < 0: continue
        hdr = s[d:s.index(':=', d)]
        # result type: after the last top-level ':' in the header
        depth = 0; colon = -1
        for k, ch in enumerate(hdr):
            if ch in '([{⦃⟨': depth += 1
            elif ch in ')]}⦄⟩': depth -= 1
            elif ch == ':' and depth == 0: colon = k
        if colon < 0: continue
        T = re.sub(r'\s+', ' ', hdr[colon + 1:]).strip()
        # body: from 'fun ' to ' := rfl'
        b0 = m.end() - len('fun ')
        b1 = s.index(' := rfl', b0)
        out.append((b0, b1, T))
    for b0, b1, T in sorted(out, reverse=True):
        s = s[:b0] + '(' + s[b0:b1] + ' :\n        ' + T + ')' + s[b1:]
        changed += 1
    open(f'{root}/{f}', 'w').write(s)
    if changed: print(f, changed)
