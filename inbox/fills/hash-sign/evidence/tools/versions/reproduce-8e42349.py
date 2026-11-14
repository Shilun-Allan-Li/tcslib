import json
import os
import pathlib
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
payload = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign')
base = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
patches = payload / 'patches'
patches.mkdir(exist_ok=True)
commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
subprocess.run(['git', 'format-patch', '--output-directory', str(patches), base + '..' + commit], cwd=repo, check=True)
index = pathlib.Path('/private/tmp/hash-sign-fill/reproduction.index')
if index.exists():
    raise SystemExit('Refusing to replace existing reproduction index')
env = dict(os.environ, GIT_INDEX_FILE=str(index))
subprocess.run(['git', 'read-tree', base], cwd=repo, env=env, check=True)
series = sorted(patches.glob('*.patch'))
for patch in series:
    subprocess.run(['git', 'apply', '--cached', str(patch)], cwd=repo, env=env, check=True)
tree = subprocess.check_output(['git', 'write-tree'], cwd=repo, env=env, text=True).strip()
expected = subprocess.check_output(['git', 'rev-parse', commit + '^{tree}'], cwd=repo, text=True).strip()
report = dict(base=base, commit=commit, patch_count=len(series), patch_names=[p.name for p in series],
    reproduced_tree=tree, expected_tree=expected, passed=tree == expected)
(payload / 'evidence/logs/patch-reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
assert report['passed']
