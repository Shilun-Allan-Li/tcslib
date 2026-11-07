"""mkbundle with optional section labels. Usage: mkbundle2.py <repo> <out.md> <list.txt>
list.txt lines: '<40-hex rev> <path> [<label>]'; the section header shows the label (default: path).
Each section is '## ===== <label> =====' + blank line + the file's bytes (+ newline if missing);
verified by splitting back and comparing with `git show <rev>:<path>`."""
import subprocess, sys, hashlib, re
repo, out, lst = sys.argv[1:4]
items = []
for l in open(lst, encoding='utf-8'):
    if not l.strip(): continue
    f = l.split()
    rev, path = f[0], f[1]; label = f[2] if len(f) > 2 else path
    assert len(rev) == 40; items.append((rev, path, label))
assert len({lab for _, _, lab in items}) == len(items), 'duplicate labels'
def show(rev, path):
    return subprocess.run(['git', '-C', repo, 'show', f'{rev}:{path}'], check=True, capture_output=True).stdout.decode('utf-8')
parts = []
for rev, path, label in items:
    body = show(rev, path)
    if not body.endswith('\n'): body += '\n'
    assert not any(x.startswith('## ===== ') for x in body.splitlines()), f'header line inside {path}'
    parts.append(f'## ===== {label} =====\n\n{body}')
open(out, 'w', encoding='utf-8').write('\n'.join(parts))
text = open(out, encoding='utf-8').read()
chunks = re.split(r'(?m)^## ===== ', text)[1:]
assert len(chunks) == len(items)
for j, ((rev, path, label), ch) in enumerate(zip(items, chunks)):
    head, _, body = ch.partition(' =====\n\n'); assert head == label, (head, label)
    want = show(rev, path)
    if not want.endswith('\n'): want += '\n'
    got = body if j == len(items) - 1 else body[:-1]
    assert body.endswith('\n') and got == want, f'mismatch in {label}'
print(f'OK {len(items)} sections verified; sha256 {hashlib.sha256(open(out,"rb").read()).hexdigest()}')
