"""Build and verify a gate bundle. Usage: mkbundle.py <repo> <out.md> <list.txt>
list.txt lines: '<40-hex rev> <path>'. Section 1 is the pack. Each section is
'## ===== <path> =====' + blank line + the file's bytes (+ newline if missing)."""
import subprocess, sys, hashlib
repo, out, lst = sys.argv[1:4]
items = [l.split(None, 1) for l in open(lst, encoding='utf-8') if l.strip()]
def show(rev, path):
    return subprocess.run(['git', '-C', repo, 'show', f'{rev}:{path}'], check=True, capture_output=True).stdout.decode('utf-8')
parts = []
for rev, path in items:
    path = path.strip(); assert len(rev) == 40
    body = show(rev, path)
    if not body.endswith('\n'): body += '\n'
    assert not any(l.startswith('## ===== ') for l in body.splitlines()), f'header line inside {path}'
    parts.append(f'## ===== {path} =====\n\n{body}')
open(out, 'w', encoding='utf-8').write('\n'.join(parts))
# verify: split back and compare
import re
text = open(out, encoding='utf-8').read()
chunks = re.split(r'(?m)^## ===== ', text)[1:]
assert len(chunks) == len(items), (len(chunks), len(items))
for j, ((rev, path), ch) in enumerate(zip(items, chunks)):
    path = path.strip(); head, _, body = ch.partition(' =====\n\n')
    assert head == path, (head, path)
    want = show(rev, path)
    if not want.endswith('\n'): want += '\n'
    # every section but the last is followed by the one '\n' that joins the sections
    got = body if j == len(items) - 1 else body[:-1]
    assert body.endswith('\n') and got == want, f'mismatch in {path}'
print(f'OK {len(items)} sections verified; sha256 {hashlib.sha256(open(out,"rb").read()).hexdigest()}')
