import re, sys
draft, probe = sys.argv[1], sys.argv[2]
d = open(draft, encoding='utf-8').read()
p = open(probe, encoding='utf-8').read()
checked = set(re.findall(r'^#check @?([^\s]+)', p, re.M))
short = {c.split('.')[-1] for c in checked}
# backtick spans
spans = re.findall(r'`([^`\n]+)`', d)
cands = set()
for s in spans:
    for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", s):
        if '_' in tok or '.' in tok or tok[0].islower():
            cands.add(tok)
missing = []
for c in sorted(cands):
    last = c.split('.')[-1]
    if c in checked or last in short or any(x.endswith('.'+c) for x in checked):
        continue
    missing.append(c)
print(len(checked), "checked")
print("\n".join(missing))
