"""Rule 11 text check: private declaration names of every other TCSlib file, and the six R3 rows,
searched as whole identifiers (last component) in the added lines' code (comments stripped).
Usage: rule11.py <repo root> <owned path> <added-lines file>"""
import os, re, sys
root, owned, added = sys.argv[1:4]
D = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|protected|nonrec|partial|unsafe)\s+)*private\s+(?:(?:noncomputable|protected|nonrec|partial|unsafe)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+([^\s(:{\[]+)')
priv = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.relpath(os.path.join(d, f), root)
        if p == owned: continue
        for l in open(os.path.join(root, p), encoding='utf-8'):
            m = D.match(l)
            if m: priv.setdefault(m.group(1).split('.')[-1], set()).add(p)
src = open(added, encoding='utf-8').read()
out = []; i = 0; depth = 0
while i < len(src):
    if src.startswith('/-', i): depth += 1; i += 2; continue
    if depth and src.startswith('-/', i): depth -= 1; i += 2; continue
    if depth: i += 1; continue
    if src.startswith('--', i):
        j = src.find('\n', i); i = len(src) if j < 0 else j; continue
    out.append(src[i]); i += 1
code = ''.join(out)
toks = set()
for t in re.findall(r"[A-Za-z_Ͱ-Ͽ][\w.'₀-₉!?Ͱ-Ͽ]*", code):
    toks.add(t); toks.add(t.split('.')[-1])
print('private names in other files:', sum(len(v) for v in priv.values()), 'declarations,', len(priv), 'distinct last components')
hits = sorted(n for n in priv if n in toks)
print('hits (last component equals a token of the added code):', len(hits))
for n in hits: print('  ', n, sorted(priv[n]))
r3 = ['copyTM_run', 'transferTM_run', 'clearTM_run', 'compareTM_run', 'incrementTM_run_succ', 'incrementTM_run_overflow']
print('R3 rows in the added code:', [r for r in r3 if r in toks])
