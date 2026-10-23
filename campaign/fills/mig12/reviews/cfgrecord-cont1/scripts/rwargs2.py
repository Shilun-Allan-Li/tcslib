import sys, re, json
# usage: rwargs2.py <head file> <unified diff pbase->head> <out json>: every identifier inside the [...]
# lists of rw/rwa/erw/simp/simp only/simpa/simpa only/dsimp/dsimp only/simp_all/simp_rw/norm_num/
# field_simp/push_cast and after unfold/delta, for each list whose text touches an added line of the
# diff (comment-stripped head code); and every show/change line among the added lines.
head, diff, outp = sys.argv[1:4]
added = set(); ln = None
for l in open(diff, encoding='utf-8'):
    m = re.match(r'^@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@', l)
    if m: ln = int(m.group(1)); continue
    if ln is None or l.startswith('+++') or l.startswith('---'): continue
    if l.startswith('+'): added.add(ln); ln += 1
    elif l.startswith('-'): pass
    else: ln += 1
src = open(head, encoding='utf-8').read()
out, i, d = [], 0, 0
while i < len(src):
    if src.startswith('/-', i): d += 1; i += 2; continue
    if src.startswith('-/', i) and d > 0: d -= 1; i += 2; continue
    out.append(src[i] if d == 0 or src[i] == '\n' else ' '); i += 1
code = '\n'.join(l.split('--')[0] for l in ''.join(out).split('\n'))
TAC = re.compile(r'\b(rw|rwa|erw|simp only|simp_all only|simp_all|simp|simpa only|simpa|norm_num only|norm_num|dsimp only|dsimp|simp_rw|field_simp|push_cast)\s*\[([^\]]*)\]', re.S)
UNF = re.compile(r'\b(unfold|delta)\s+([A-Za-z_][\w.\']*(?:[ \t]+[A-Za-z_][\w.\']*)*)')
ids = {}; nlists = 0; nocc = 0
def lineof(off): return code.count('\n', 0, off) + 1
for m in TAC.finditer(code):
    a, b = lineof(m.start()), lineof(m.end())
    if not any(x in added for x in range(a, b + 1)): continue
    nlists += 1
    for arg in m.group(2).split(','):
        arg = re.sub(r'^\s*←\s*', '', arg).strip()
        tok = arg.split()[0] if arg else ''
        tok = tok.lstrip('(@')
        if re.match(r"^[A-Za-z_Ͱ-Ͽ][\w.'₀-₉!?]*$", tok) or tok.startswith('↓'):
            ids.setdefault(tok, []).append(a); nocc += 1
for m in UNF.finditer(code):
    a = lineof(m.start())
    if a in added:
        for t in m.group(2).split(): ids.setdefault(t, []).append(a); nocc += 1
shows = [(n, code.split('\n')[n - 1].strip()) for n in sorted(added) if re.search(r'\b(show|change)\b', code.split('\n')[n - 1])]
json.dump({'ids': ids, 'shows': shows}, open(outp, 'w'), indent=1)
print('added lines', len(added), 'lists touching them', nlists, 'occurrences', nocc, 'distinct identifiers', len(ids), 'show/change lines', len(shows))
