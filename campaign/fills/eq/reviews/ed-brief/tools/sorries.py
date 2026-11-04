"""Topological check of an order list and a comment-stripped sorry census over it.
usage: python3 -I sorries.py <worktree> <order.txt> <overlay-file> <overlaid-path>"""
import os, re, sys
wt, orderf, overlay, opath = sys.argv[1:5]
order = [l.strip() for l in open(orderf) if l.strip()]
def text(m):
    if m == opath: return open(overlay, encoding='utf-8').read()
    return open(os.path.join(wt, m + '.lean'), encoding='utf-8').read()
def strip(s):
    # keep line structure: blank out block comments (nested-unaware but adequate here) and line comments
    out = []; i = 0; depth = 0; n = len(s)
    while i < n:
        if s.startswith('/-', i):
            depth += 1; i += 2; out.append('  '); continue
        if depth and s.startswith('-/', i):
            depth -= 1; i += 2; out.append('  '); continue
        if depth:
            out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            out.append(' ' * (j + 1 - i)); i = j + 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)
pos = {m: k for k, m in enumerate(order)}
bad = 0
for m in order:
    for mm in re.finditer(r'^\s*import\s+(TCSlib\S*)', strip(text(m)), re.M):
        d = mm.group(1).replace('.', '/')
        if d not in pos or pos[d] > pos[m]:
            bad += 1; print('ORDER VIOLATION', m, '<-', d)
print('order violations:', bad)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|instance|abbrev|structure|example)\s+([^\s:({\[]+)', re.M)
TOK = re.compile(r"(?<![A-Za-z0-9_.'])sorry(?![A-Za-z0-9_'])")
tot = 0
for m in order:
    s = strip(text(m)); lines = s.split('\n')
    decls = [(s[:mm.start()].count('\n') + 1, mm.group(1)) for mm in DECL.finditer(s)]
    names = []
    for ln, l in enumerate(lines, 1):
        for _ in TOK.finditer(l):
            owner = '?'
            for dl, dn in decls:
                if dl <= ln: owner = dn
                else: break
            names.append(owner)
    if names:
        tot += len(set(names))
        print(f"{m}: {len(set(names))}: {', '.join(sorted(set(names), key=names.index))}")
print('TOTAL sorried declarations', tot)
