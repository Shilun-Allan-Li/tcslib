"""Inspection table for the E-D fill's new code (python3 -I inspect.py <owned.lean> <audit.out>).
Scans region (b) and the target's body for the identifiers named in `rw`/`simp`/`simp only`/
`dsimp only`/`unfold`/`simp_all` argument lists and in `show` steps, and classifies each against the
audit walk's list of other-file TCSlib constants (`EXT name : kind module`): own (this file),
other-file TCSlib definition, other-file TCSlib theorem, or core/Mathlib/local. Prints the counts
and every row naming an other-file TCSlib definition (rule 10 allows none in rewrite lists)."""
import re, sys
src, audit = sys.argv[1], sys.argv[2]
L = open(src, encoding='utf-8').read().split('\n')
start = next(i for i, l in enumerate(L) if l.startswith("/-! ### The diagonalizer's leaf"))
ext = {}
for l in open(audit, encoding='utf-8'):
    m = re.match(r'EXT (\S+) : (\S+) (\S+)', l)
    if m: ext[m.group(1)] = (m.group(2), m.group(3))
short = {}
for n, k in ext.items():
    for i in range(len(n.split('.'))):
        short.setdefault('.'.join(n.split('.')[i:]), []).append((n, k))
rows = []
for i in range(start, len(L)):
    l = L[i]
    for kw, rx in [('rw', r'\b(?:rw|rwa|nth_rw \d+)\s*\[([^\]]*)'), ('simp', r'\bsimp(?:_all)?(?: only)?\s*\[([^\]]*)'),
                   ('dsimp', r'\bdsimp only\s*\[([^\]]*)'), ('unfold', r'\bunfold\s+([^\n]*)'),
                   ('show', r'\bshow\s+(.*)')]:
        for m in re.finditer(rx, l):
            for tok in re.findall(r"[A-Za-z_][A-Za-z_0-9.'₀-₉]*", m.group(1)):
                if tok in ('at', 'by', 'fun', 'if', 'then', 'else', 'from', 'with'): continue
                rows.append((i + 1, kw, tok))
own = lambda t: re.match(r"(dz|Dz|qy|Qy|κ|h|e|c|seg|L|P|T|Z)", t) is not None
cls = {}
bad = []
for ln, kw, tok in rows:
    cand = short.get(tok) or short.get(tok.split('.')[-1]) if '.' not in tok else short.get(tok)
    if tok.startswith(('dz', 'Dz', 'qy', 'Qy', 'κ.')):
        c = 'own'
    elif cand:
        kinds = {k[0] for _, k in cand}
        c = 'TCSlib-' + '/'.join(sorted(kinds))
        if 'def' in kinds and kw in ('rw', 'simp', 'dsimp', 'unfold'):
            bad.append((ln, kw, tok, cand))
    else:
        c = 'core/Mathlib/local'
    cls[(kw, c)] = cls.get((kw, c), 0) + 1
print('rows', len(rows))
for (kw, c), n in sorted(cls.items()):
    print(f'{kw:7s} {c:28s} {n}')
print('other-file TCSlib definitions named in rw/simp/dsimp/unfold lists:', len(bad))
for b in bad: print('  ', b)
shows = [(ln, tok) for ln, kw, tok in rows if kw == 'show']
