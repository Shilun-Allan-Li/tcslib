import json
import os
from pathlib import Path
import subprocess
import sys

root = Path.cwd()
store = Path(os.environ.get('XDG_CACHE_HOME', str(Path.home() / '.cache'))) / 'mathlib'
print(f'archive_store={store}; exists={store.exists()}')
files = [p for p in store.rglob('*') if p.is_file()] if store.exists() else []
print(f'archive_store_files={len(files)}; bytes={sum(p.stat().st_size for p in files)}')
print('origin=pre-existing host store; individual origin unknown')
print(f'host_toolchain={Path.home() / ".elan/toolchains/leanprover--lean4---v4.25.0"}')
manifest = json.loads((root / 'lake-manifest.json').read_text())
bad = []
present = 0
for p in manifest['packages']:
    name = p['name'].strip('«»')
    path = root / '.lake/packages' / name
    if not path.exists():
        print(f'ABSENT {name}')
        continue
    present += 1
    actual = []
    for args in [['remote', 'get-url', 'origin'], ['rev-parse', 'HEAD']]:
        actual.append(subprocess.check_output(['git', '-C', str(path)] + args,
                                             text=True).strip())
    ok = actual == [p['url'], p['rev']]
    print(f'{"MATCH" if ok else "MISMATCH"} {name}: {actual}')
    if not ok:
        bad.append(name)
print(f'PACKAGE PINS {"PASS" if not bad else "FAIL"}: {present} present; '
      f'{len(manifest["packages"]) - present} absent; {len(bad)} mismatches')
sys.exit(bool(bad))
