"""Append `#print axioms` for every public declaration of a Lean file (read-only on its input).

Usage: python3 -I mkaxprobe.py <in.lean> <out.lean>
Comment-aware and namespace-qualified, as tools/axprobe.py; the probe is the file itself plus the
appended commands, so it needs no olean of the file.
"""
import re
import sys

src, out = sys.argv[1:3]
KW = r'(theorem|lemma|def|abbrev|structure|inductive|opaque|instance)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec)\s+)*)' + KW + r'\s+([^\s(:{\[]+)')
t = open(src, encoding='utf-8').read()
def strip(s):
    o, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i): depth += 1; i += 2; continue
        if s.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
        if depth == 0: o.append(s[i])
        elif s[i] == '\n': o.append('\n')
        i += 1
    return '\n'.join(l.split('--')[0] for l in ''.join(o).split('\n'))
ns, res = [], []
for l in strip(t).split('\n'):
    m = re.match(r'^namespace\s+(\S+)', l)
    if m: ns.append(m.group(1)); continue
    m = re.match(r'^end\s+(\S+)\s*$', l)
    if m and ns and ns[-1] == m.group(1): ns.pop(); continue
    m = DECL.match(l)
    if m and 'private' not in (m.group(1) or '') and m.group(2) != 'instance':
        n = m.group(3); res.append(n[7:] if n.startswith('_root_.') else '.'.join(ns + [n]))
assert not ns, ns
assert len(res) == len(set(res)), 'duplicate names'
open(out, 'w', encoding='utf-8').write(t.rstrip('\n') + '\n\n' + ''.join(f'#print axioms {n}\n' for n in res))
print(len(res), 'publics probed')
