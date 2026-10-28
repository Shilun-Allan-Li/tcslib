"""Extract the comment/docstring text of head lines [a, b] and scan it for campaign labels (python3 -I).
usage: python3 -I newtext.py <file> <a> <b> [<a> <b> ...]"""
import re, sys
L = open(sys.argv[1], encoding='utf-8').read().split('\n')
spans = list(zip(map(int, sys.argv[2::2]), map(int, sys.argv[3::2])))
text = []
for a, b in spans:
    depth = 0; cur = []
    for i in range(a - 1, b):
        l = L[i]; j = 0; s = ''
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('-/', j) and depth: depth -= 1; j += 2; continue
            if depth: s += l[j]
            j += 1
        if s.strip(): cur.append(f'{i+1}: {s.strip()}')
    text += cur
print('\n'.join(text))
pat = re.compile(r'\b(E-Q|E-D|E-DUP|E-SERIAL|C1-E|C1E|L[1-6]|checkpoint|gate|brief|megafill|maintainer|fill|session|REPORT|route|probe|campaign|audit|ruling|20\d\d-\d\d|qy_|rv_|M₁|Codex|Claude|escalat\w*|pre-ship|dossier)\b', re.I)
hits = [(t, m.group(0)) for t in text for m in pat.finditer(t)]
print('LABEL HITS:', hits if hits else 'none')
