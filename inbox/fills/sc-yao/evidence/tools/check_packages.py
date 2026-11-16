#!/usr/bin/env python3
"""Compare every present dependency's origin URL and HEAD with the pinned manifest."""
import json
from pathlib import Path
import subprocess

manifest = json.loads(Path('lake-manifest.json').read_text())
errors = []
present = absent = 0
for package in manifest['packages']:
    name = package['name'].strip('«»')
    root = Path(manifest['packagesDir']) / name
    if not root.exists():
        print('ABSENT', name)
        absent += 1
        continue
    present += 1
    url = subprocess.check_output(['git', '-C', str(root), 'remote', 'get-url', 'origin'],
                                  text=True).strip()
    rev = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    ok = url == package['url'] and rev == package['rev']
    print('MATCH' if ok else 'MISMATCH', name, url, rev)
    if not ok:
        errors.append(name)
print(f'PACKAGES {present} present / {absent} absent; mismatches {len(errors)}')
raise SystemExit(bool(errors))
