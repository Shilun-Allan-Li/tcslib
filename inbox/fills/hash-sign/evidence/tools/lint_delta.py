import difflib
import json
import pathlib
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
out = ev / 'escalations'
out.mkdir(exist_ok=True)
def failures(path):
    return {tuple(line.split(None, 2)[1:]) for line in path.read_text().splitlines() if line.startswith('FAIL ')}
base = failures(ev / 'logs/lint-base.log')
current = failures(ev / 'logs/lint-current-1.log')
added = sorted(current - base)
(out / 'lint-new-fails.json').write_text(json.dumps(added, indent=2) + '\n')
path = 'TCSlib/Cryptography/Authentication.lean'
old = (repo / path).read_text()
imports = []
for _, message in added:
    module = message.split('`')[1]
    imports.append('import ' + module + '\n')
anchor = 'import TCSlib.Cryptography.Authentication.Signatures.HashAndSign\n'
new = old.replace(anchor, anchor + ''.join(imports))
(out / 'proposed-authentication-imports.patch').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True), fromfile='a/' + path, tofile='b/' + path)))
print('baseline FAIL:', len(base), 'current FAIL:', len(current), 'new:', len(added))
for item in added:
    print(*item)
