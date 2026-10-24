"""Append `#print axioms` for every public theorem/lemma/def of a module (python3 -I mkax.py <in> <out>)."""
import re, sys
src = open(sys.argv[1], encoding='utf-8').read()
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((protected|noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev)\s+([^\s(:{\[]+)')
stack, names, depth = [], [], 0
for l in src.split('\n'):
    d0 = depth
    j = 0
    while j < len(l):
        if l.startswith('/-', j): depth += 1; j += 2; continue
        if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
        if depth == 0 and l.startswith('--', j): break
        j += 1
    if d0 > 0: continue
    m = re.match(r'^namespace\s+(\S+)', l)
    if m: stack.append(('ns', m.group(1))); continue
    m = re.match(r'^section\b\s*(\S*)', l)
    if m: stack.append(('sec', m.group(1))); continue
    m = re.match(r'^end\b\s*(\S*)', l)
    if m and stack: stack.pop(); continue
    if l.startswith('private'): continue
    m = DECL.match(l)
    if m:
        n = m.group(5)
        ns = '.'.join(x for k, x in stack if k == 'ns')
        names.append(n if n.startswith('_root_.') else (ns + '.' + n if ns else n))
assert not stack, stack
with open(sys.argv[2], 'w', encoding='utf-8') as f:
    f.write(src.rstrip('\n') + '\n\n' + ''.join(f'#print axioms {n}\n' for n in names))
print(len(names), 'names')
