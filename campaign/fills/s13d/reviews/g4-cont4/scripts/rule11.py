import sys, re, os
root, diff = sys.argv[1], sys.argv[2]
R3 = ['copyTM_run', 'transferTM_run', 'clearTM_run', 'compareTM_run', 'incrementTM_run_succ', 'incrementTM_run_overflow']
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*private\s+(?:(?:noncomputable|nonrec|partial|unsafe|protected)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)')
privs = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(d, f)
        if p.endswith('Build/ZoneRebalance.lean'): continue
        for l in open(p, encoding='utf-8', errors='replace'):
            m = DECL.match(l)
            if m: privs.setdefault(m.group(1), set()).add(os.path.relpath(p, root))
# added code lines
added = []
for l in open(diff, encoding='utf-8'):
    if l.startswith('+') and not l.startswith('+++'): added.append(l[1:])
text = '\n'.join(added)
# strip comments
out = []; i = 0; depth = 0
while i < len(text):
    if text.startswith('/-', i): depth += 1; i += 2; continue
    if depth and text.startswith('-/', i): depth -= 1; i += 2; continue
    if depth: i += 1; continue
    if text.startswith('--', i):
        j = text.find('\n', i); i = len(text) if j < 0 else j; continue
    out.append(text[i]); i += 1
code = ''.join(out)
tokens = set(re.findall(r"[A-Za-z_][\w.'₀-₉?!]*", code))
print('private declarations in other TCSlib files:', len(privs), 'names')
hits = sorted(n for n in privs if n in tokens or any(t.endswith('.' + n) for t in tokens if '.' in t and t.split('.')[-1] == n))
print('other-file private names occurring as identifiers in the added code:', len(hits))
for h in hits: print('  ', h, sorted(privs[h])[:3])
for r in R3: print('R3', r, 'occurrences in added code:', len(re.findall(r'\b' + re.escape(r) + r'\b', code)))
new_privs = re.findall(r'^\s*private\s+(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|structure|instance)\s+(\S+)', code, re.M)
print('new private declarations in added lines:', len(new_privs), '; not zr_-prefixed:', [n for n in new_privs if not n.startswith('zr_')])
