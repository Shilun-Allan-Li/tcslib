"""Private declarations of a file reached only from given public declarations. Read-only.
Usage: python3 -I retire.py <file.lean> <public name> ...
Prints the private declarations that the named public declarations reach (identifier closure
over comment-stripped code) and that no other public declaration of the file reaches, with
their line counts (code, and with the preceding docstring)."""
import os
import re
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import scan  # noqa: E402
from region import strip_comments, doc_start  # noqa: E402

path, roots = sys.argv[1], sys.argv[2:]
ds, lines = scan(path)
code = strip_comments(lines)
names = {d['name'] for d in ds}
uses = {}
for d in ds:
    toks = set()
    for l in code[d['line'] - 1:d['end']]:
        for t in re.findall(r"[A-Za-z_][A-Za-z0-9_'!?.]*", l):
            toks.update(t.split('.'))
    uses[d['name']] = {t for t in toks if t in names and t != d['name']}
priv = {d['name'] for d in ds if d['private']}
# instances of reached inductives are reached implicitly
for d in ds:
    if d['kind'] == 'instance' and d['private']:
        for t in list(uses[d['name']]):
            uses.setdefault(t, set()).add(d['name'])


def closure(rs):
    seen, st = set(), list(rs)
    while st:
        x = st.pop()
        for y in uses.get(x, ()):
            if y in priv and y not in seen:
                seen.add(y); st.append(y)
    return seen


mine = closure(roots)
others = closure([d['name'] for d in ds if not d['private'] and d['name'] not in roots])
only = sorted((d for d in ds if d['name'] in mine - others), key=lambda d: d['line'])
tot = totd = 0
for d in only:
    n = d['end'] - d['line'] + 1
    nd = d['end'] - doc_start(lines, d['line']) + 1
    tot += n; totd += nd
    print(d['line'], d['name'], n, nd)
print(f'{len(only)} declarations; {tot} code lines; {totd} lines with docstrings')
