"""Locate declaration headers by (possibly dotted) short name in the comment-stripped Lean sources
of a checkout. Prints name => path:line kind [private]. usage: python3 -I finddecl.py <root> name..."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines
root, names = sys.argv[1], sys.argv[2:]
H = re.compile(r'^[ \t]*(?:@\[[^\]]*\][ \t]*)*((?:(?:private|protected|noncomputable|scoped)\s+)*)'
               r'(def|abbrev|theorem|lemma|inductive|structure|class|instance)\s+([^\s(:{\[]+)', re.M)
idx = {}
for dp, dn, fn in os.walk(os.path.join(root, 'TCSlib')):
    for f in fn:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); rel = os.path.relpath(p, root)
        t = strip_keep_lines(open(p, encoding='utf-8').read())
        for m in H.finditer(t):
            nm = m.group(3); ln = t.count('\n', 0, m.start(2)) + 1
            for k in {nm, nm.split('.')[-1]}:
                idx.setdefault(k, []).append((rel, ln, m.group(2), 'private' in m.group(1), nm))
for n in names:
    hits = idx.get(n, [])
    exact = [h for h in hits if h[4] == n or h[4].endswith('.' + n)]
    for rel, ln, k, pv, full in (exact or hits)[:6]:
        print(f'{n} => {rel.replace("TCSlib/Complexity/","")}:{ln} {k} {full}{" [private]" if pv else ""}')
    if not hits: print(f'{n} => NOT FOUND')
