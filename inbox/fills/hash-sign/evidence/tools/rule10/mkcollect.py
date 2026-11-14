"""mkcollect.py <nm-review NmCollect.lean> <modules file> <title> <out.lean>: the nm-cca2 review collector
(PkCollect lineage) with its owner list and imports replaced by <modules> (verbatim otherwise)."""
import sys, re
tmpl, modsf, title, out = sys.argv[1:5]
mods = [l.strip().replace('/', '.') for l in open(modsf) if l.strip()]
s = open(tmpl, encoding='utf-8').read()
a = s.index('def owners : List Name := ['); b = s.index(']', a)
s = s[:a] + 'def owners : List Name := [\n  ' + ',\n  '.join('`' + m for m in mods) + s[b:]
s = re.sub(r'^import TCSlib\S*\n', '', s, flags=re.M)
s = s.replace('import Lean\n', 'import Lean\n' + ''.join(f'import {m}\n' for m in mods), 1)
s = re.sub(r'/-! nm-cca2 review collector.*?-/', f'/-! {title}: CLOSURE/ROOT for the owners, CAT for every TCSlib definition. -/', s, flags=re.S)
open(out, 'w', encoding='utf-8').write(s)
