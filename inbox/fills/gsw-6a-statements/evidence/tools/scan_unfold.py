"""scan_unfold.py <collector-lines.log> <path>...: the explicit-unfold scan of Rule 10.
For every new or changed Lean file, every identifier passed to `simp`/`simp only`/`simp_all`/`dsimp`/
`simp?`/`rw`/`rwa`/`rewrite`/`nth_rewrite`/`nth_rw`/`erw`/`simp_rw` (inside their `[...]` lists, `←`
allowed), or named by `unfold`/`delta`/`unfold_let`, is resolved against the collector's CAT rows
(every TCSlib definition, with its home module) by full name or by namespace suffix. A hit whose
home module is not the file's own module is a FOREIGN-UNFOLD (Rule 10 breach unless notation: a
reducible abbreviation or `PolyExpr.eval`). Comments and strings are blanked first."""
import sys, re, json
log = sys.argv[1]; paths = sys.argv[2:]
cat = {}
for l in open(log, encoding='utf8'):
    if l.startswith('CAT '):
        r = json.loads(l[4:]); cat[r['name']['display']] = r
bysuffix = {}
for n in cat:
    parts = n.split('.')
    for k in range(len(parts)):
        bysuffix.setdefault('.'.join(parts[k:]), []).append(n)
def blank(s):
    out = []; i = 0; depth = 0
    while i < len(s):
        if s.startswith('/-', i): depth += 1; out.append('  '); i += 2; continue
        if depth and s.startswith('-/', i): depth -= 1; out.append('  '); i += 2; continue
        if depth: out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); j = len(s) if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
        if s[i] == '"':
            j = i + 1
            while j < len(s) and s[j] != '"': j += 2 if s[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)
TAC = re.compile(r'\b(simp_all|simp_rw|simp\?|simp|dsimp|rwa|rw|rewrite|nth_rewrite|nth_rw|erw)\b(\s+only)?[^\[\n]*?\[')
total = 0
for p in paths:
    mod = p[:-5].replace('/', '.')
    s = blank(open(p, encoding='utf8').read())
    hits = []
    for m in TAC.finditer(s):
        i = m.end(); d = 1; j = i
        while j < len(s) and d:
            if s[j] == '[': d += 1
            elif s[j] == ']': d -= 1
            j += 1
        for a in s[i:j - 1].split(','):
            a = a.strip().lstrip('←').strip()
            mm = re.match(r"^@?([A-Za-z_][\w.'₀-₉]*)", a)
            if mm: hits.append((s[:i].count('\n') + 1, m.group(1), mm.group(1)))
    for m in re.finditer(r'\b(unfold|delta|unfold_let)\s+([^\n]*)', s):
        for a in m.group(2).split():
            if re.match(r"^[A-Za-z_][\w.']*$", a) and a not in ('at', 'in'):
                hits.append((s[:m.start()].count('\n') + 1, m.group(1), a))
    for line, tac, ident in hits:
        cands = cat.get(ident) and [ident] or bysuffix.get(ident, [])
        foreign = [c for c in cands if cat[c]['home']['display'] != mod]
        own = [c for c in cands if cat[c]['home']['display'] == mod]
        if foreign and not own:
            r = cat[foreign[0]]
            note = 'notation' if r['abbrev'] or r['status'] == 'reducible' or foreign[0] == 'Complexity.PolyExpr.eval' else 'FOREIGN-UNFOLD'
            print(f'{note}\t{p}:{line}\t{tac}\t{ident} -> {", ".join(foreign)} ({r["home"]["display"]})')
            total += note == 'FOREIGN-UNFOLD'
print(f'RESULT foreign_unfolds={total} files={len(paths)}')
