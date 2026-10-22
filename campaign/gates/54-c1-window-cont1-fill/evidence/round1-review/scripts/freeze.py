"""Statement freeze between two versions of a module: per declaration (kind, visibility, name),
the comment-stripped header from the keyword to the `:=`/`where` that opens its body."""
import re, sys
def strip_comments(t):
    out, i, depth = [], 0, 0
    while i < len(t):
        if t.startswith('/-', i): depth += 1; i += 2; continue
        if depth and t.startswith('-/', i): depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if t.startswith('--', i):
            j = t.find('\n', i); i = len(t) if j < 0 else j; continue
        out.append(t[i]); i += 1
    return ''.join(out)
DECL = re.compile(r'^(private\s+)?(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s({:\[]+)', re.M)
def decls(path):
    t = strip_comments(open(path, encoding='utf-8').read())
    ms = list(DECL.finditer(t)); res = {}
    for k, m in enumerate(ms):
        end = ms[k + 1].start() if k + 1 < len(ms) else len(t)
        chunk = t[m.start():end]
        cut, depth, i = len(chunk), 0, 0
        while i < len(chunk):
            ch = chunk[i]
            if ch in '([{⟨': depth += 1
            elif ch in ')]}⟩': depth -= 1
            elif depth == 0 and (chunk.startswith(':=', i) or re.match(r'\bwhere\b', chunk[i:])
                                 and (i == 0 or not chunk[i - 1].isalnum())):
                cut = i; break
            i += 1
        head = ' '.join(chunk[:cut].split())
        body = ' '.join(chunk[cut:].split())
        res[m.group(3)] = ('private' if m.group(1) else 'public', m.group(2), head, body)
    return res
a, b = decls(sys.argv[1]), decls(sys.argv[2])
pub = lambda d: sorted(n for n, v in d.items() if v[0] == 'public')
prv = lambda d: sorted(n for n, v in d.items() if v[0] == 'private')
print('public before/after:', len(pub(a)), len(pub(b)), ' private before/after:', len(prv(a)), len(prv(b)))
print('public added:', sorted(set(pub(b)) - set(pub(a))), ' public removed:', sorted(set(pub(a)) - set(pub(b))))
for n in pub(a):
    if n in b:
        print(f'public {n}: statement identical: {a[n][2] == b[n][2]}; body changed: {a[n][3] != b[n][3]}')
print('private removed:', sorted(set(prv(a)) - set(prv(b))))
print('private added:', sorted(set(prv(b)) - set(prv(a))))
print('private statement changed:', sorted(n for n in set(prv(a)) & set(prv(b)) if a[n][2] != b[n][2]))
print('private body changed only:', sorted(n for n in set(prv(a)) & set(prv(b)) if a[n][2] == b[n][2] and a[n][3] != b[n][3]))
