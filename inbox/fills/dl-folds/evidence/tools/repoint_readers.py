#!/usr/bin/env python3
"""R1/R2/R3 re-pointing of the NM files (dl-folds checkpoint 2).

1. `obtain ⟨p₁, …⟩ := fields_input …` / `fields_finInput …` / `polyTimeComputable_rd` /
   `polyTimeComputable_finFields` become one `have` per named component, from the published
   per-reader lemmas (same arguments, same line breaks).
2. Projections `(fields_input …).1` etc. become the per-reader lemma.
3. The reader names: rdU→rU, rdZ→rZ, rdW→rW, rdState→rS, rdIdx→rI, rdQuery→rX, rdLog→rL,
   rdAns→rAns; finU→rU, finZ→rZ, finW→rW, finL→rL, finSt→rS (finA keeps its short name).
usage: repoint_readers.py FILE...
"""
import re, sys

IH = 'InteractiveHandler.'
TABLES = {
    'fields_input': ['rU_input', 'rZ_input', 'rW_input', 'rS_input', 'rI_input', 'rX_input',
                     'rL_input'],
    'fields_finInput': ['rU_finInput', 'rZ_finInput', 'rW_finInput', 'finA_finInput',
                        'rL_finInput'],
    'polyTimeComputable_rd': ['polyTimeComputable_rU', 'polyTimeComputable_rZ',
                              'polyTimeComputable_rW', 'polyTimeComputable_rS',
                              'polyTimeComputable_rI', 'polyTimeComputable_rX',
                              'polyTimeComputable_rL', 'polyTimeComputable_rAns'],
    'polyTimeComputable_finFields': ['polyTimeComputable_rU', 'polyTimeComputable_rZ',
                                     'polyTimeComputable_rW', 'polyTimeComputable_finA',
                                     'polyTimeComputable_rL'],
}
RENAME = {'rdAns_input': 'InteractiveHandler.rAns_input',
          'polyTimeComputable_finSt': 'InteractiveHandler.polyTimeComputable_rS',
          'finSt_finInput': 'InteractiveHandler.rS_finInput', 'rdU': 'rU', 'rdZ': 'rZ', 'rdW': 'rW', 'rdState': 'rS', 'rdIdx': 'rI',
          'rdQuery': 'rX', 'rdLog': 'rL', 'rdAns': 'rAns', 'finU': 'rU', 'finZ': 'rZ',
          'finW': 'rW', 'finL': 'rL', 'finSt': 'rS'}


def proj_index(p):
    # `.1` -> 0, `.2.1` -> 1, ..., `.2.2...2` (k twos, no .1) -> k
    parts = p.strip('.').split('.')
    if parts[-1] == '1':
        return len(parts) - 1
    return len(parts)


def transform(src):
    lines = src.split('\n')
    out, i = [], 0
    pat = re.compile(r'^(\s*)obtain ⟨([^⟩]*)⟩ := (fields_input|fields_finInput|polyTimeComputable_rd|'
                     r'polyTimeComputable_finFields)\b(.*)$')
    while i < len(lines):
        m = pat.match(lines[i])
        if not m:
            out.append(lines[i]); i += 1; continue
        ind, names, lem, rest = m.group(1), m.group(2), m.group(3), m.group(4)
        cont = []
        j = i + 1
        while j < len(lines) and lines[j].strip() and \
                len(lines[j]) - len(lines[j].lstrip()) > len(ind):
            cont.append(lines[j]); j += 1
        comps = [c.strip() for c in names.split(',')]
        for k, c in enumerate(comps):
            if c == '-':
                continue
            out.append(f'{ind}have {c} := {IH}{TABLES[lem][k]}{rest}')
            out.extend(cont)
        i = j
    src = '\n'.join(out)
    # projections
    def proj(mm):
        lem, args, p = mm.group(1), mm.group(2), mm.group(3)
        return f'{IH}{TABLES[lem][proj_index(p)]}{args}'
    src = re.sub(r'\((fields_input|fields_finInput)((?: [^()]+| \([^()]*\))*)\)((?:\.[12])+)',
                 proj, src)
    src = re.sub(r'\b(polyTimeComputable_rd|polyTimeComputable_finFields)()((?:\.[12])+)', proj, src)
    for o, n in RENAME.items():
        src = re.sub(r'(?<![\w.])' + o + r'(?![\w\'])', n, src)
    return src


for f in sys.argv[1:]:
    s = open(f).read()
    t = transform(s)
    if t != s:
        open(f, 'w').write(t)
        print('changed', f)
