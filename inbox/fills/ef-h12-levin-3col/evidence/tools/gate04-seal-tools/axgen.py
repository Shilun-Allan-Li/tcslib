import re, sys
root, lst, out = sys.argv[1:4]
files = [l.strip() for l in open(lst) if l.strip()]
names, mods = [], []
for f in files:
    src = open(f"{root}/{f}", encoding='utf-8').read()
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    src = re.sub(r'--[^\n]*', '', src)
    ns = []
    for line in src.split('\n'):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r'^(?:@\[[^\]]*\]\s*)?(?:protected\s+)?(?:nonrec\s+)?(?:theorem|lemma)\s+([^\s(:{\[]+)', line)
        if m and not line.lstrip().startswith('private'):
            n = m.group(1)
            full = n[len('_root_.'):] if n.startswith('_root_.') else '.'.join(ns + [n])
            names.append(full)
    mods.append(f[:-5].replace('/', '.'))
with open(out, 'w', encoding='utf-8') as o:
    for md in mods: o.write(f'import {md}\n')
    o.write('\n')
    for n in names: o.write(f'#print axioms {n}\n')
print(len(names), 'theorems in', len(mods), 'files')
