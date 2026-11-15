#!/usr/bin/env python3
"""For each declaration of the given files: its proof length (lines from the declaration line to the
line before the next declaration/docstring/section marker) and whether its docstring has a
`**Proof sketch.**` (or `**Proof sketch**`) paragraph. Reports proofs of 15 lines or more without one.
usage: sketchcheck.py FILE..."""
import re, sys
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure)\b\s*([^\s:({\[]*)')
bad = 0
for f in sys.argv[1:]:
    L = open(f, encoding='utf-8').read().split('\n')
    starts = [i for i, l in enumerate(L) if DECL.match(l)]
    for k, i in enumerate(starts):
        m = DECL.match(L[i]); name = m.group(2) or m.group(1)
        # the docstring just above
        j = i - 1; doc = []
        if j >= 0 and L[j].rstrip().endswith('-/'):
            while j >= 0:
                doc.append(L[j])
                if L[j].lstrip().startswith('/--'): break
                j -= 1
        doc = '\n'.join(reversed(doc))
        # end: next line that starts a docstring, a declaration, a section marker or `end`
        e = i + 1
        while e < len(L) and not (L[e].startswith('/-') or DECL.match(L[e]) or
                                  re.match(r'^(end|section|namespace|variable|open|attribute)\b', L[e])):
            e += 1
        # proof length: from the line with ':= by' or ' :=' to e
        p = next((t for t in range(i, e) if re.search(r':=\s*(by)?\s*$|:= by|\bwhere\s*$', L[t])), None)
        n = 0 if p is None else len([x for x in L[p + 1:e] if x.strip()])
        has = 'Proof sketch' in doc
        flag = n >= 15 and not has
        bad += flag
        print(f'{"MISSING" if flag else "ok     "} {f.split("/")[-1]}:{i + 1} {name} proof={n} sketch={has}')
print('RESULT', 'OK' if bad == 0 else f'{bad} long proofs without a sketch')
