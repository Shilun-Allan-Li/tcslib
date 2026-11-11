"""Verify every present dependency against the issue manifest; never mutate packages."""
import json
import subprocess
from pathlib import Path

manifest = json.loads(Path('lake-manifest.json').read_text())
bad = []
absent = []
for package in manifest['packages']:
    name = package['name'].strip('«»')
    path = Path('.lake/packages') / name
    if not path.exists():
        absent.append(name)
        print(f'{name}: ABSENT')
        continue
    url = subprocess.check_output(['git', '-C', str(path), 'remote', 'get-url', 'origin'], text=True).strip()
    rev = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    match = url == package['url'] and rev == package['rev']
    print(f'{name}: {"MATCH" if match else "MISMATCH"} {url} {rev}')
    if not match:
        bad.append(name)
assert not bad, 'E-RES: package mismatch: ' + ', '.join(bad)
roots = Path('../pack/order.txt').read_text().splitlines()
for module in roots:
    imports = [line.split()[1] for line in Path(module + '.lean').read_text().splitlines() if line.startswith('import ')]
    assert all(not any(mod.startswith(name + '.') for name in absent) for mod in imports)
print('Package pin check: PASS (all present packages match; order imports no absent package)')
