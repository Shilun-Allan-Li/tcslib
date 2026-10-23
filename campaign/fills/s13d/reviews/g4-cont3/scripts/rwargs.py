import re, sys
# usage: rwargs.py <added-lines file>: identifiers inside the [...] argument lists of rw/rwa/simp/simp only/
# simpa/norm_num/dsimp/unfold/delta/field_simp/simp_rw/conv rw, joined over continuation lines.
txt = open(sys.argv[1], encoding='utf-8').read()
ids = set()
for m in re.finditer(r'\b(rw|rwa|erw|simp only|simp|simpa only|simpa|norm_num only|norm_num|dsimp only|dsimp|simp_rw|unfold|delta|push_cast)\s*\[([^\]]*)\]', txt, re.S):
    for a in m.group(2).split(','):
        a = a.strip()
        a = re.sub(r'^←\s*', '', a)
        a = a.split()[0] if a else a
        if re.match(r"^[A-Za-z_][A-Za-z0-9_.'₀-₉!?]*$", a): ids.add(a)
for m in re.finditer(r'\b(unfold|delta)\s+([A-Za-z_][\w.\']*(?:\s+[A-Za-z_][\w.\']*)*)', txt):
    for a in m.group(2).split(): ids.add(a)
print(' '.join(sorted(ids)))
