"""Rule 11 grep: added lines of a unified diff vs the six R3 rows and every private declaration name
of another TCSlib file, and the prefix of every new private. usage: rule11.py <worktree> <owned file> <diff>"""
import os, re, sys
root, owned, dp = sys.argv[1:4]
names = {}
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        p = os.path.join(d, f)
        if not f.endswith('.lean') or os.path.relpath(p, root) == owned: continue
        for line in open(p, encoding='utf-8'):
            m = re.match(r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?private\s+(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s:({\[]+)', line)
            if m: names.setdefault(m.group(1).split('.')[-1], set()).add(os.path.relpath(p, root))
r3 = ['copyTM_run', 'transferTM_run', 'clearTM_run', 'compareTM_run', 'incrementTM_run_succ', 'incrementTM_run_overflow']
lines = [l[1:] for l in open(dp, encoding='utf-8') if l.startswith('+') and not l.startswith('+++')]
toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.₀-₉]*", '\n'.join(lines))); toks |= {t.split('.')[-1] for t in toks}
print('other-file private names collected: %d (unique short names)' % len(names))
print('%d added lines; R3-row token hits: %s' % (len(lines), sorted(t for t in toks if t in r3) or 'none'))
hp = sorted(t for t in toks if t in names)
print('other-file private-name token hits: %s' % (hp or 'none'))
for t in hp:
    ctx = [l.strip()[:110] for l in lines if re.search(r'(?<![A-Za-z0-9_])' + re.escape(t) + r'(?![A-Za-z0-9_])', l)][:2]
    print('    %s: private in %s; occurrence(s): %s' % (t, sorted(names[t])[:3], ctx))
newp = re.findall(r'^private\s+(?:theorem|def|instance|abbrev)\s+(\S+)', '\n'.join(lines), re.M)
print('new privates: %d; not ic_-prefixed: %s' % (len(newp), [n for n in newp if not n.startswith('ic_')] or 'none'))
