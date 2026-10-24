import re, sys
src = open(sys.argv[1], encoding='utf-8').read()
probe = set(l.strip() for l in open(sys.argv[2]))
idents = set()
for m in re.finditer(r'`([^`\n]+)`', src):
    tok = m.group(1)
    if '/' in tok or tok.endswith(('.md', '.txt', '.py', '.lean', '.zip', '.sh')): continue
    for w in re.findall(r"(?<![A-Za-z0-9_.'])([A-Za-z_][A-Za-z0-9_'₀-₉]*(?:\.[A-Za-z_][A-Za-z0-9_'₀-₉]*)*)", tok):
        if '_' in w or re.search(r'[a-z][A-Z]', w) or '.' in w:
            idents.add(w)
suffixes = set()
for p in probe:
    parts = p.split('.')
    for i in range(len(parts)):
        suffixes.add('.'.join(parts[i:]))
for w in sorted(idents):
    print(('IN ' if w in suffixes else 'NOT ') + w)
