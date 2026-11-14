import json, subprocess
from pathlib import Path
manifest=json.loads(Path('lake-manifest.json').read_text())
mismatch=[]
for package in manifest['packages']:
 name=package['name'].strip('«»')
 directory=Path('.lake/packages')/name
 if not directory.exists():print(f'ABSENT {name}');continue
 url=subprocess.check_output(['git','-C',str(directory),'remote','get-url','origin'],text=True).strip()
 rev=subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'],text=True).strip()
 okay=url==package['url'] and rev==package['rev']
 print(f'{"OK" if okay else "MISMATCH"} {name} URL={url} HEAD={rev}')
 if not okay:mismatch.append(name)
print('PACKAGES MATCH: all present packages match manifest' if not mismatch else 'PACKAGES MISMATCH: '+','.join(mismatch))
raise SystemExit(bool(mismatch))
