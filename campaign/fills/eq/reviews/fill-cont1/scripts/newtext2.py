"""Comment and docstring text of head lines [a, b] (pairs), scanned for campaign labels
(python3 -I).  Own private names (qy_/Qy) are not labels; they are counted separately.
usage: python3 -I newtext2.py <file> <a> <b> [<a> <b> ...]"""
import re, sys
from collections import Counter
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
spans = list(zip(map(int, sys.argv[2::2]), map(int, sys.argv[3::2])))
text = []
for a, b in spans:
    depth = 0
    for i in range(a - 1, b):
        l = L[i]; j = 0; s = ''
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('-/', j) and depth: depth -= 1; j += 2; continue
            if depth: s += l[j]
            elif l.startswith('--', j): s += l[j:]; break
            j += 1
        if s.strip(): text.append((i + 1, s.strip()))
LAB = re.compile(r'\b(E-Q|E-D|E-DUP|E-SERIAL|E-RES|C1-E|C1E|cont1|L[1-6]|checkpoint\w*|gate\w*|brief\w*|megafill|maintainer|'
                 r'fill\w*|session|REPORT|probe\w*|campaign|audit\w*|ruling|20\d\d-\d\d-\d\d|Codex|Claude|'
                 r'escalat\w*|pre-ship|dossier|finding\w*|backlog|worker|reviewer|route note|MIG-1|R3|deviation\w*)\b')
PATH = re.compile(r'(audits/|campaign/|exchange/|devtools/|\.md\b)')
hits = [(n, m.group(0), t) for n, t in text for m in LAB.finditer(t)]
paths = [(n, m.group(0), t) for n, t in text for m in PATH.finditer(t)]
print(f'comment/docstring lines: {len(text)}')
print('LABEL HITS:', len(hits))
for n, w, t in hits: print(f'   {n}: [{w}] {t[:150]}')
print('PATH HITS:', len(paths))
for n, w, t in paths: print(f'   {n}: [{w}] {t[:150]}')
own = Counter(m.group(0) for _, t in text for m in re.finditer(r'\b(qy\w*|Qy\w*)', t))
print('own private names cited in the text (distinct):', len(own))
lc = [(n, t) for n, t in text if t.startswith('--')]
print('line comments (--):', len(lc))
for n, t in lc: print(f'   {n}: {t[:150]}')
