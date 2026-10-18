"""Declaration-level freeze check between a base file and a proposed file: comment-stripped
text of every base declaration must reappear verbatim in the proposed file, in the same order;
list declarations added. Usage: freeze.py BASE PROPOSED"""
import re, sys
def strip(t):
    t = re.sub(r'/-.*?-/', '', t, flags=re.S)       # block and doc comments (no nesting here)
    t = re.sub(r'--[^\n]*', '', t)
    return t
kw = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                r'(def|theorem|lemma|abbrev|structure|inductive|instance|class)\s+([^\s:({\[]+)', re.M)
def decls(path):
    t = strip(open(path, encoding='utf-8').read())
    ms = list(kw.finditer(t))
    out = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        body = t[m.start():end]
        body = re.sub(r'\n\s*(namespace|end|section|variable|open|set_option)\b[^\n]*', '\n', body)
        body = '\n'.join(l.rstrip() for l in body.strip().split('\n') if l.strip())
        out.append((m.group(2), body))
    return out
base, prop = decls(sys.argv[1]), decls(sys.argv[2])
pn = [n for n, _ in prop]; pd = dict(prop)
missing = [n for n, _ in base if n not in pd]
changed = [n for n, b in base if n in pd and pd[n] != b]
order = [pn.index(n) for n, _ in base if n in pd]
added = [n for n in pn if n not in dict(base)]
print(f"base declarations: {len(base)}; proposed: {len(prop)}")
print(f"base declarations missing in proposed: {len(missing)} {missing}")
print(f"base declarations whose comment-stripped text changed: {len(changed)} {changed}")
print(f"base order preserved: {order == sorted(order)}")
print(f"added declarations ({len(added)}):")
for n in added: print("  " + n)
