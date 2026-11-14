import json
import pathlib
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
manifest = json.loads((repo / 'lake-manifest.json').read_text())
bad = []
for p in manifest['packages']:
    name = p['name'].strip('«»')
    directory = repo / '.lake/packages' / name
    if not directory.exists():
        print(name, 'ABSENT')
        continue
    def git(*args):
        return subprocess.check_output(['git', '-C', str(directory), *args], text=True).strip()
    url, rev = git('remote', 'get-url', 'origin'), git('rev-parse', 'HEAD')
    ok = url == p['url'] and rev == p['rev']
    print(name, 'MATCH' if ok else 'MISMATCH', url, rev)
    if not ok:
        bad.append(name)
print('PRESENT PACKAGE PINS PASS' if not bad else 'E-RES package mismatch: ' + ', '.join(bad))
raise SystemExit(bool(bad))
