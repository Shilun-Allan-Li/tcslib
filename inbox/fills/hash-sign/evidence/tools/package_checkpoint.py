import hashlib
import pathlib
import shutil
import subprocess
import sys

commit, dest_arg = sys.argv[1:]
repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
current = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign')
dest = pathlib.Path(dest_arg)
if dest.exists():
    raise SystemExit('Refusing to replace existing snapshot: ' + str(dest))
dest.mkdir(parents=True)
shutil.copy2(current / 'REPORT.md', dest / 'REPORT.md')
ev = dest / 'evidence'
ev.mkdir()
for name in ['inputs', 'tools', 'rule10']:
    shutil.copytree(current / 'evidence' / name, ev / name)
logs = ev / 'logs'
logs.mkdir()
for p in (current / 'evidence/logs').iterdir():
    if p.is_dir():
        if p.name == 'bootstrap':
            shutil.copytree(p, logs / p.name)
        continue
    if p.name.startswith(('collision-game-', 'forward-game-')):
        continue
    if p.name.startswith('owned-check-') and p.name not in [f'owned-check-{i}.log' for i in range(1, 5)]:
        continue
    shutil.copy2(p, logs / p.name)
base = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
full = subprocess.check_output(['git', 'rev-parse', commit], cwd=repo, text=True).strip()
(logs / 'checkpoint-source-commit.txt').write_text(full + '\n')
paths = subprocess.check_output(['git', 'diff', '--name-only', base, full], cwd=repo, text=True).splitlines()
for path in paths:
    target = dest / 'src' / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(subprocess.check_output(['git', 'show', full + ':' + path], cwd=repo))
patches = dest / 'patches'
patches.mkdir()
subprocess.run(['git', 'format-patch', '--output-directory', str(patches), base + '..' + full], cwd=repo, check=True)
files = sorted(p for p in ev.rglob('*') if p.is_file())
manifest = ev / 'SHA256SUMS'
manifest.write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(ev).as_posix() + '\n' for p in files))
expected = {line.split('  ', 1)[1] for line in manifest.read_text().splitlines()}
actual = {p.relative_to(ev).as_posix() for p in ev.rglob('*') if p.is_file() and p != manifest}
assert expected == actual
for path in paths:
    assert (dest / 'src' / path).read_bytes() == subprocess.check_output(['git', 'show', full + ':' + path], cwd=repo)
print('Snapshot:', dest, 'source:', full, 'source files:', len(paths), 'evidence files:', len(files))
