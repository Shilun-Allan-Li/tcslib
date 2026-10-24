"""rule11.py <base worktree> <owned file rel> <base file> <head file> : the added lines (difflib) vs the six R3 rows
and every private declaration name of another TCSlib file (token level)."""
import difflib, os, re, sys
root, owned, bf, hf = sys.argv[1:5]
names = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        p = os.path.join(d, f)
        if not f.endswith('.lean') or os.path.relpath(p, root) == owned or f.startswith('F3C2Rev'): continue
        for line in open(p, encoding='utf-8'):
            m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|protected\s+)*private\s+(?:noncomputable\s+|nonrec\s+|partial\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)', line)
            if m: names.setdefault(m.group(1).split('.')[-1], set()).add(os.path.relpath(p, root))
a = open(bf, encoding='utf-8').read().split('\n'); b = open(hf, encoding='utf-8').read().split('\n')
lines = []
for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
    if tag in ('replace', 'insert'): lines += b[j1:j2]
r3 = ['copyTM_run', 'transferTM_run', 'clearTM_run', 'compareTM_run', 'incrementTM_run_succ', 'incrementTM_run_overflow']
toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", '\n'.join(lines))); toks |= {t.split('.')[-1] for t in toks}
print('other-file private names collected: %d (unique short names)' % len(names))
print('%d added lines; R3-row hits: %s' % (len(lines), sorted(t for t in toks if t in r3) or 'none'))
hp = sorted(t for t in toks if t in names)
print('other-file private-name token hits: %s' % (hp or 'none'))
for t in hp:
    ctx = [l.strip()[:110] for l in lines if re.search(r'(?<![A-Za-z0-9_])' + re.escape(t) + r'(?![A-Za-z0-9_])', l)][:2]
    print('    %s: private in %s; occurrence(s): %s' % (t, sorted(names[t])[:3], ctx))
newpriv = [re.match(r'^private\s+(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)', l) for l in lines]
newpriv = [m.group(1) for m in newpriv if m]
print('new/changed private declaration headers in the added lines:', len(newpriv), '; all cw_-prefixed:', all(n.startswith('cw_') for n in newpriv))
