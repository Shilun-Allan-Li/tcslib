"""Hygiene of the added lines of a diff (comments and docstrings stripped for code checks).
usage: python3 -I hygiene.py <diff> <head file>"""
import re, sys
d = open(sys.argv[1], encoding='utf-8').read().split('\n')
add = [l[1:] for l in d if l.startswith('+') and not l.startswith('+++')]
print('added lines:', len(add))
# strip comments from the head file to get code-only added text
src = open(sys.argv[2], encoding='utf-8').read()
out, i, depth = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
    out.append(src[i] if depth == 0 else ('\n' if src[i] == '\n' else ' ')); i += 1
code = [l.split('--')[0] for l in ''.join(out).split('\n')]
hl = src.split('\n')
addset = set()
# map added lines to head line numbers via hunk headers
ln = None
for l in d:
    m = re.match(r'^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@', l)
    if m: ln = int(m.group(1)); continue
    if ln is None or l.startswith('---') or l.startswith('+++'): continue
    if l.startswith('+'): addset.add(ln); ln += 1
    elif l.startswith('-'): pass
    else: ln += 1
pats = {k: re.compile(v) for k, v in {
  'sorry': r'\bsorry\b', 'admit': r'\badmit\b', 'axiom': r'^\s*axiom\b|\baxiom\s', 'unfold': r'\bunfold\b',
  'delta': r'\bdelta\b', 'set_option': r'\bset_option\b', 'open': r'^\s*open\b', 'section': r'^\s*section\b',
  'variable': r'^\s*variable\b', 'attribute': r'^\s*attribute\b|@\[', 'native_decide': r'native_decide',
  'decide': r'\bdecide\b', 'implemented_by/extern': r'implemented_by|extern', 'unsafe/partial': r'\bunsafe\b|\bpartial\b',
  'macro/elab/syntax': r'^\s*(macro|elab|syntax|macro_rules|elab_rules)\b', 'run_cmd/#eval': r'run_cmd|#eval|#print|#check',
  'Lean.ofReduceBool/trustCompiler': r'ofReduceBool|trustCompiler', 'show': r'\bshow\b', 'change': r'\bchange\b',
  'rfl': r'\brfl\b', 'simp/simpa (any)': r'\bsimp\b|\bsimpa\b|\bsimp only\b', 'dsimp': r'\bdsimp\b', 'nomatch': r'\bnomatch\b',
  'noncomputable': r'\bnoncomputable\b', 'Classical': r'Classical'}.items()}
for k, p in pats.items():
    hits = [(n, hl[n-1].strip()[:110]) for n in sorted(addset) if p.search(code[n-1])]
    print(f'{k}: {len(hits)}')
    if k in ('unfold', 'open', 'attribute', 'decide', 'noncomputable', 'Classical', 'set_option', 'section', 'variable', 'axiom', 'sorry', 'admit', 'delta', 'native_decide', 'nomatch'):
        for h in hits: print('    %5d: %s' % h)
w = [(n, len(hl[n-1])) for n in range(1, len(hl)+1) if len(hl[n-1]) > 100]
print('lines over 100 characters (whole file):', w)
print('max added-line width:', max(len(hl[n-1]) for n in addset))
