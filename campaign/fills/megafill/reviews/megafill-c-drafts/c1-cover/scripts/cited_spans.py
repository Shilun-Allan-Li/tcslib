import re, sys
b = open(sys.argv[1], encoding='utf-8').read()
# drop fenced code blocks, keep them separately
fences = re.findall(r'```.*?```', b, flags=re.S)
b2 = re.sub(r'```.*?```', ' ', b, flags=re.S).replace('\n', ' ')
p = open(sys.argv[2], encoding='utf-8').read()
checked = set(re.findall(r'#check @(\S+)', p))
norm = lambda s: s.replace('Turing.', '')
cn = {norm(c) for c in checked}
spans = re.findall(r'`([^`]+)`', b2)
toks = set()
for s in spans:
    for t in re.findall(r"[A-Za-z_][A-Za-z0-9_.'₀₁₂]*", s):
        toks.add(t)
cands = sorted(t for t in toks if ('.' in t or '_' in t) and not t.endswith(('.md','.txt','.lean','.py','.sh','.zip')))
for t in cands:
    if norm(t) not in cn:
        print(t)
