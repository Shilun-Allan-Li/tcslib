import re, sys
s = open(sys.argv[1], encoding='utf-8').read()
s = re.sub(r'--[^\n]*', '', s)
out = set()
for m in re.finditer(r'\b(rw|rwa|simp only|simp|simpa only|simpa|dsimp only|dsimp)\s*\[', s):
    i = m.end(); depth = 1; j = i
    while depth:
        if s[j] == '[': depth += 1
        elif s[j] == ']': depth -= 1
        j += 1
    for a in s[i:j-1].replace('\n', ' ').split(','):
        a = a.strip().lstrip('←').strip()
        a = a.split(' ')[0]
        if a: out.add((m.group(1), a))
for m in re.finditer(r'\bunfold\s+([^\n]+)', s):
    for a in m.group(1).split(): out.add(('unfold', a))
for m in re.finditer(r'\b(show|change)\b', s):
    out.add((m.group(1), '(present)'))
for k, a in sorted(out, key=lambda x: (x[1], x[0])):
    print(f'{a}\t{k}')
