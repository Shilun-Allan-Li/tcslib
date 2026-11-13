#!/usr/bin/env python3
"""Assemble the dl-folds delivery under the exchange checkout.

usage: pack.py DEST   (DEST = <exchange>/inbox/fills/dl-folds)

* src/: every file changed or added between the issue base and HEAD of /workspace/folds;
* patches/: `git format-patch` of the whole series from the issue base;
* evidence/: /workspace/foldpay/evidence, the tools of /workspace/foldtools, and the seal
  sources of /workspace/folds/scratch/seal (evidence/seal-src/<tag>/);
* evidence/SHA256SUMS over every evidence file; then a check that the delivered evidence paths are
  exactly the manifest's paths.
REPORT.md is written separately (copied from /workspace/foldpay/REPORT.md if present).
"""
import hashlib, os, shutil, subprocess, sys

BASE = 'd3f2290a2c66f614e8807903b89ac595086578b3'
REPO = '/workspace/folds'
dest = sys.argv[1]
assert dest.rstrip('/').endswith('inbox/fills/dl-folds'), dest
if os.path.exists(dest):
    shutil.rmtree(dest)
os.makedirs(dest)

# src/
names = subprocess.run(['git', 'diff', '--name-only', '--diff-filter=AM', BASE, 'HEAD'], cwd=REPO,
                       capture_output=True, text=True, check=True).stdout.split()
for n in names:
    os.makedirs(os.path.dirname(f'{dest}/src/{n}'), exist_ok=True)
    blob = subprocess.run(['git', 'show', f'HEAD:{n}'], cwd=REPO, capture_output=True, check=True).stdout
    open(f'{dest}/src/{n}', 'wb').write(blob)
deleted = subprocess.run(['git', 'diff', '--name-only', '--diff-filter=D', BASE, 'HEAD'], cwd=REPO,
                         capture_output=True, text=True, check=True).stdout.split()

# patches/
os.makedirs(f'{dest}/patches')
subprocess.run(['git', 'format-patch', '-q', '-o', f'{dest}/patches', f'{BASE}..HEAD'], cwd=REPO,
               check=True)

# evidence/
ev = f'{dest}/evidence'
shutil.copytree('/workspace/foldpay/evidence', ev)
os.makedirs(f'{ev}/tools', exist_ok=True)
for f in sorted(os.listdir('/workspace/foldtools')):
    p = f'/workspace/foldtools/{f}'
    if os.path.isfile(p) and (f.endswith('.py') or f.endswith('.sh')):
        shutil.copy(p, f'{ev}/tools/{f}')
for tag in sorted(os.listdir(f'{REPO}/scratch/seal')):
    shutil.copytree(f'{REPO}/scratch/seal/{tag}', f'{ev}/seal-src/{tag}')
if os.path.exists(f'{ev}/SHA256SUMS'):
    os.remove(f'{ev}/SHA256SUMS')
files = []
for root, _, fs in os.walk(ev):
    for f in fs:
        files.append(os.path.relpath(os.path.join(root, f), ev))
files.sort()
with open(f'{ev}/SHA256SUMS', 'w') as out:
    for f in files:
        h = hashlib.sha256(open(f'{ev}/{f}', 'rb').read()).hexdigest()
        out.write(f'{h}  {f}\n')
# completeness check
listed = {l.split('  ', 1)[1].rstrip('\n') for l in open(f'{ev}/SHA256SUMS')}
present = set()
for root, _, fs in os.walk(ev):
    for f in fs:
        r = os.path.relpath(os.path.join(root, f), ev)
        if r != 'SHA256SUMS':
            present.add(r)
assert listed == present, (listed ^ present)
if os.path.exists('/workspace/foldpay/REPORT.md'):
    shutil.copy('/workspace/foldpay/REPORT.md', f'{dest}/REPORT.md')
print(f'src {len(names)} files (deleted at HEAD: {deleted}); patches '
      f'{len(os.listdir(dest + "/patches"))}; evidence {len(files)} files, manifest == delivery')
