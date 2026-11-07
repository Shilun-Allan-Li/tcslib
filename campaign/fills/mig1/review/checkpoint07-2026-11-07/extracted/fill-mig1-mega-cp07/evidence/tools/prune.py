"""prune.py <repo> <file> [--apply]: delete private declarations of a module that are reachable
from no public declaration of the module (name-token reachability over comment-stripped code;
declaration chunks from devtools/seyoon/declfreeze.py). Prints the deletion list."""
import os, re, sys
repo, f = sys.argv[1], sys.argv[2]; apply = '--apply' in sys.argv
code = open(os.path.join(repo, 'devtools/seyoon/declfreeze.py'), encoding='utf-8').read()
code = code[:code.index('a = chunks(open(sys.argv[1])')]; ns = {}; exec(compile(code, 'df', 'exec'), ns)
path = os.path.join(repo, f); text = open(path, encoding='utf-8').read()
ch = ns['chunks'](text)
def strip(t):
    out = []; i = 0; d = 0
    while i < len(t):
        if t.startswith('/-', i): d += 1; i += 2; continue
        if d and t.startswith('-/', i): d -= 1; i += 2; continue
        if d: i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i); i = len(t) if j < 0 else j; continue
        out.append(t[i]); i += 1
    return ''.join(out)
short = lambda n: n.split('.')[-1]
priv = {}
for n, p, t in ch:
    if p: priv.setdefault(short(n), []).append(n)
tok = re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉!?]*")
refs = {}
for n, p, t in ch:
    body = strip(t)
    refs[n] = set(x.split('.')[-1] for x in tok.findall(body)) | set(tok.findall(body))
# non-chunk text (attributes, etc.) also roots
roots = [n for n, p, t in ch if not p]
reach = set(); stack = list(roots)
while stack:
    n = stack.pop()
    if n in reach: continue
    reach.add(n)
    for r in refs.get(n, ()):
        for full in priv.get(r, []):
            if full not in reach: stack.append(full)
dead = [(n, t) for n, p, t in ch if p and n not in reach]
print(f'private {sum(1 for _,p,_ in ch if p)} public {len(roots)} dead {len(dead)} lines {sum(t.count(chr(10))+1 for _,t in dead)}')
for n, t in dead: print('DEAD', n)
if apply:
    for n, t in dead:
        assert text.count(t) == 1, n
        text = text.replace(t + '\n', '', 1) if (t + '\n') in text else text.replace(t, '', 1)
    text = re.sub(r'\n{3,}', '\n\n', text)
    open(path, 'w', encoding='utf-8').write(text)
    print('applied')
