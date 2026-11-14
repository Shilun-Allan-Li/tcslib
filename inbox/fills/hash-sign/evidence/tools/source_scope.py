import hashlib
import json
import pathlib
import re
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
base = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
owner = 'TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean'
directory = owner.removesuffix('.lean') + '/'
facade = 'TCSlib/Cryptography/Authentication.lean'
def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo, text=True)
commit = git('rev-parse', 'HEAD').strip()
changed = git('diff', '--name-only', base, commit).splitlines()
assert all(p in [owner, facade] or p.startswith(directory) for p in changed)
old = git('show', base + ':' + owner)
new = git('show', commit + ':' + owner)
start = 'theorem hashAndSign_oneTimeSecure '
def header(text):
    return text[text.index(start):].split(':= by', 1)[0]
assert header(old) == header(new)
namespace = 'namespace TCSlib.Cryptography.Authentication\n'
section = '/-! ### Theorem 144.1 -/'
assert old.split(namespace, 1)[1].split(section, 1)[0] == new.split(namespace, 1)[1].split(section, 1)[0]
tail = '/-- **The existential form of Theorem 144.1**'
assert old[old.index(tail):] == new[new.index(tail):]
old_facade, new_facade = git('show', base + ':' + facade), git('show', commit + ':' + facade)
added_imports = [line for line in new_facade.splitlines(keepends=True) if line.startswith('import ') and line not in old_facade.splitlines(keepends=True)]
assert len(added_imports) == 8
assert all(line.startswith('import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.') for line in added_imports)
anchor = 'import TCSlib.Cryptography.Authentication.Signatures.HashAndSign\n'
assert new_facade == old_facade.replace(anchor, anchor + ''.join(added_imports))
files = []
for path in changed:
    source = git('show', commit + ':' + path)
    lines = len(source.splitlines())
    assert lines < 1000
    if path.startswith(directory):
        assert not re.search(r'@\[\s*simp(?:\s|\])|attribute\s*\[\s*simp(?:\s|\])', source)
        assert not re.search(r'\bsorry\b', source)
    files.append(dict(path=path, lines=lines, sha256=hashlib.sha256(source.encode()).hexdigest()))
report = dict(base=base, commit=commit, target_header_identical=True,
    other_original_declarations_identical=True, scope_pass=True,
    authorized_parent_imports=[s.strip() for s in added_imports], files=files)
(ev / 'logs/source-scope.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
