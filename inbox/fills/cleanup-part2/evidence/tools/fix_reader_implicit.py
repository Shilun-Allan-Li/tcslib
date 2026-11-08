#!/usr/bin/env python3
"""Ascribe the definition's result type to the left-hand side of generated `<name>_def` readers
whose binders contain implicit arguments (so implicit arguments fixed only by the result type are
determined). python3 -I fix_reader_implicit.py <root> <file>..."""
import sys, re
root = sys.argv[1]
for f in sys.argv[2:]:
    s = open(f'{root}/{f}').read(); edits = []
    for m in re.finditer(r"((?:private )?theorem (\S+)_def ([^\n]*)):\n    ([^\n]*) =\n", s):
        name, binders, lhs = m.group(2), m.group(3), m.group(4)
        if '{' not in binders or lhs.startswith('('): continue
        short = name.split('.')[-1]
        d = s.rfind(f'def {name} ', 0, m.start())
        if d < 0: continue
        hdr = s[d:s.index(':=', d)]
        depth = 0; colon = -1
        for k, ch in enumerate(hdr):
            if ch in '([{⦃⟨': depth += 1
            elif ch in ')]}⦄⟩': depth -= 1
            elif ch == ':' and depth == 0: colon = k
        if colon < 0: continue
        T = re.sub(r'\s+', ' ', hdr[colon + 1:]).strip()
        a = m.start(4); b = m.end(4)
        edits.append((a, b, f'({lhs} : {T})'))
    for a, b, t in sorted(edits, reverse=True): s = s[:a] + t + s[b:]
    open(f'{root}/{f}', 'w').write(s)
    if edits: print(f, len(edits))
