#!/usr/bin/env python3
"""Assemble the prf-mac delivery under the exchange checkout.

usage: deliver.py STAGE DEST   (STAGE = cp1 | cp2 | final; DEST = <exchange>/inbox/fills/prf-mac)

1. patches/: `git format-patch` of the whole series from the issue base to HEAD of the proof
   branch, and patches/COMMITS.tsv (hash, author name/email/date, committer name/email/date);
2. the reproduction check: a scratch clone at the issue base applies the series with `git am`,
   the committer of each row set from COMMITS.tsv, and must reproduce every hash
   (log: evidence/amcheck/amcheck-STAGE.log, written before the evidence is copied);
3. src/: every file added or changed between the issue base and HEAD;
4. evidence/: /workspace/prfpay/evidence, the tools of /workspace/prftools (evidence/tools/) and
   the seal and probe sources of /workspace/prfmac/scratch (evidence/scratch-src/), with
   evidence/SHA256SUMS over every evidence file; the delivered evidence paths must equal the
   manifest's paths;
5. REPORT.md from /workspace/prfpay/REPORT-STAGE.md;
6. the top-level SHA256SUMS over every delivered file except itself; again the delivered paths
   must equal the manifest's paths.
"""
import hashlib, os, shutil, subprocess, sys

BASE = '107f1e8c218733eac12d6b9bee6fece441271317'
REPO = '/workspace/prfmac'
PAY = '/workspace/prfpay'
stage, dest = sys.argv[1], sys.argv[2]
assert stage in ('cp1', 'cp2', 'final'), stage
assert dest.rstrip('/').endswith('inbox/fills/prf-mac'), dest


def git(*a, cwd=REPO, env=None):
    return subprocess.run(['git', *a], cwd=cwd, capture_output=True, text=True, check=True,
                          env=env).stdout


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


def manifest(root, out_name, skip_self=True):
    files = []
    for r, _, fs in os.walk(root):
        for f in fs:
            rel = os.path.relpath(os.path.join(r, f), root)
            if rel != out_name:
                files.append(rel)
    files.sort()
    with open(os.path.join(root, out_name), 'w') as out:
        for f in files:
            out.write(f'{sha(os.path.join(root, f))}  {f}\n')
    listed = {l.split('  ', 1)[1].rstrip('\n') for l in open(os.path.join(root, out_name))}
    present = set()
    for r, _, fs in os.walk(root):
        for f in fs:
            rel = os.path.relpath(os.path.join(r, f), root)
            if rel != out_name:
                present.add(rel)
    assert listed == present, sorted(listed ^ present)
    return len(files)


if os.path.exists(dest):
    shutil.rmtree(dest)
os.makedirs(dest)

# 1. patches and COMMITS.tsv
os.makedirs(f'{dest}/patches')
git('format-patch', '-q', '-o', f'{dest}/patches', f'{BASE}..HEAD')
rows = git('log', '--reverse', '--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI',
           f'{BASE}..HEAD').splitlines()
with open(f'{dest}/patches/COMMITS.tsv', 'w') as out:
    out.write('hash\tauthor_name\tauthor_email\tauthor_date\t'
              'committer_name\tcommitter_email\tcommitter_date\n')
    for r in rows:
        out.write(r + '\n')

# 2. reproduction check in a scratch clone
os.makedirs(f'{PAY}/evidence/amcheck', exist_ok=True)
log = [f'reproduction check ({stage}): scratch clone of the proof repository at the issue base '
       f'{BASE}; `git am` of each patch with GIT_COMMITTER_NAME/EMAIL/DATE from COMMITS.tsv']
tmp = '/workspace/prfpay/amclone'
if os.path.exists(tmp):
    shutil.rmtree(tmp)
subprocess.run(['git', 'clone', '-q', '--no-checkout', REPO, tmp], check=True)
git('checkout', '-q', '--detach', BASE, cwd=tmp)
patches = sorted(p for p in os.listdir(f'{dest}/patches') if p.endswith('.patch'))
assert len(patches) == len(rows), (patches, rows)
ok = True
for p, r in zip(patches, rows):
    h, an, ae, ad, cn, ce, cd = r.split('\t')
    env = dict(os.environ, GIT_COMMITTER_NAME=cn, GIT_COMMITTER_EMAIL=ce, GIT_COMMITTER_DATE=cd)
    git('-c', 'user.name=x', '-c', 'user.email=x@x', 'am', '-q', f'{dest}/patches/{p}', cwd=tmp,
        env=env)
    got = git('rev-parse', 'HEAD', cwd=tmp).strip()
    same = got == h
    ok &= same
    log.append(f'{p}\texpected {h}\tgot {got}\t{"OK" if same else "MISMATCH"}')
tree_ok = git('rev-parse', 'HEAD^{tree}', cwd=tmp).strip() == git('rev-parse', 'HEAD^{tree}').strip()
log.append(f'final tree equal to the proof branch: {tree_ok}')
log.append('RESULT ' + ('all hashes reproduced' if ok and tree_ok else 'FAILED'))
open(f'{PAY}/evidence/amcheck/amcheck-{stage}.log', 'w').write('\n'.join(log) + '\n')
shutil.rmtree(tmp)
assert ok and tree_ok, log

# 3. src
names = git('diff', '--name-only', '--diff-filter=AM', BASE, 'HEAD').split()
deleted = git('diff', '--name-only', '--diff-filter=D', BASE, 'HEAD').split()
assert not deleted, deleted
for n in names:
    os.makedirs(os.path.dirname(f'{dest}/src/{n}'), exist_ok=True)
    blob = subprocess.run(['git', 'show', f'HEAD:{n}'], cwd=REPO, capture_output=True,
                          check=True).stdout
    open(f'{dest}/src/{n}', 'wb').write(blob)

# 4. evidence
ev = f'{dest}/evidence'
shutil.copytree(f'{PAY}/evidence', ev)
os.makedirs(f'{ev}/tools', exist_ok=True)
for f in sorted(os.listdir('/workspace/prftools')):
    p = f'/workspace/prftools/{f}'
    if os.path.isfile(p) and (f.endswith('.py') or f.endswith('.sh')):
        shutil.copy(p, f'{ev}/tools/{f}')
for d in ('seal', 'ax', 'controls', 'probe', 'census'):
    if os.path.isdir(f'{REPO}/scratch/{d}'):
        shutil.copytree(f'{REPO}/scratch/{d}', f'{ev}/scratch-src/{d}')
for f in os.listdir(f'{REPO}/scratch'):
    if f.endswith('.lean') and os.path.isfile(f'{REPO}/scratch/{f}'):
        os.makedirs(f'{ev}/scratch-src', exist_ok=True)
        shutil.copy(f'{REPO}/scratch/{f}', f'{ev}/scratch-src/{f}')
if os.path.exists(f'{ev}/SHA256SUMS'):
    os.remove(f'{ev}/SHA256SUMS')
nev = manifest(ev, 'SHA256SUMS')

# 5. REPORT.md
shutil.copy(f'{PAY}/REPORT-{stage}.md', f'{dest}/REPORT.md')

# 6. top-level manifest
ntop = manifest(dest, 'SHA256SUMS')
print(f'{stage}: patches {len(patches)} (+ COMMITS.tsv, hashes reproduced); src {len(names)} files; '
      f'evidence {nev} files (manifest == delivery); top-level manifest {ntop} files '
      f'(== delivery)')
