#!/usr/bin/env python3
"""Assemble the gsw-6b-u12 payload (COMMON §8). usage: deliver.py STAGE DEST
STAGE = cp1 | final; DEST = <exchange checkout>/inbox/fills/gsw-6b-u12.
1. patches/: `git format-patch <base>..HEAD` of fill/gsw-6b-u12, and patches/COMMITS.tsv (hash, author
   name/email/date, committer name/email/date, signing);
2. C13: in the scratch clone /workspace/gsw/amclone (sparse: the owned file), reset to the base, `git am`
   each patch with GIT_COMMITTER_NAME/EMAIL/DATE from COMMITS.tsv; every hash must be reproduced
   (log evidence/reproduce-STAGE.log, written before evidence/ is copied);
3. src/: every owned file at HEAD (`git show HEAD:<path>`), checked equal to the reproduced clone's file;
4. evidence/: /workspace/gsw/evidence plus tools (evidence/tools/), with evidence/SHA256SUMS;
5. REPORT.md from /workspace/gsw/REPORT-STAGE.md;
6. top-level SHA256SUMS over every delivered file except itself (paths equal the delivered files)."""
import hashlib, os, shutil, subprocess, sys
BASE = 'bff0567b6c4b6b724c8fd20ff3ef92258eb3fc9d'
REPO, AM, W = '/workspace/gsw/repo', '/workspace/gsw/amclone', '/workspace/gsw'
OWNED = ['TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Branching.lean']
stage, dest = sys.argv[1], sys.argv[2]
assert stage in ('cp1', 'final') and dest.rstrip('/').endswith('inbox/fills/gsw-6b-u12')
def git(*a, cwd=REPO, env=None):
    return subprocess.run(['git', *a], cwd=cwd, capture_output=True, text=True, check=True,
                          env=env).stdout
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
def manifest(root, name):
    files = sorted(os.path.relpath(os.path.join(r, f), root) for r, _, fs in os.walk(root) for f in fs)
    files = [f for f in files if f != name]
    with open(os.path.join(root, name), 'w') as o:
        for f in files:
            o.write(f'{sha(os.path.join(root, f))}  {f}\n')
    listed = {l.split('  ', 1)[1].rstrip('\n') for l in open(os.path.join(root, name))}
    present = {os.path.relpath(os.path.join(r, f), root) for r, _, fs in os.walk(root) for f in fs} - {name}
    assert listed == present
    return len(files)
if os.path.exists(dest):
    shutil.rmtree(dest)
os.makedirs(f'{dest}/patches')
head = git('rev-parse', 'HEAD').strip()
git('format-patch', '-q', '-o', f'{dest}/patches', f'{BASE}..HEAD')
rows = git('log', '--reverse', '--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09%G?',
           f'{BASE}..HEAD').splitlines()
with open(f'{dest}/patches/COMMITS.tsv', 'w') as o:
    o.write('hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\t'
            'committer_date\tsigning\n')
    for r in rows:
        p = r.split('\t')
        o.write('\t'.join(p[:7] + ['none' if p[7] == 'N' else p[7]]) + '\n')
log = [f'C13 reproduction ({stage}): scratch clone {AM} (sparse, the owned file), reset to the base {BASE};'
       f' `git am` of each patch with GIT_COMMITTER_NAME/EMAIL/DATE from COMMITS.tsv']
git('checkout', '-q', '--detach', BASE, cwd=AM)
git('reset', '-q', '--hard', BASE, cwd=AM)
patches = sorted(p for p in os.listdir(f'{dest}/patches') if p.endswith('.patch'))
assert len(patches) == len(rows)
ok = True
for p, r in zip(patches, rows):
    h, an, ae, ad, cn, ce, cd, _ = r.split('\t')
    env = dict(os.environ, GIT_COMMITTER_NAME=cn, GIT_COMMITTER_EMAIL=ce, GIT_COMMITTER_DATE=cd)
    git('-c', 'user.name=x', '-c', 'user.email=x@x', '-c', 'commit.gpgsign=false', 'am', '-q',
        f'{dest}/patches/{p}', cwd=AM, env=env)
    got = git('rev-parse', 'HEAD', cwd=AM).strip()
    ok &= got == h
    log.append(f'{p}\texpected {h}\tgot {got}\t{"OK" if got == h else "MISMATCH"}')
for f in OWNED:
    os.makedirs(os.path.dirname(f'{dest}/src/{f}'), exist_ok=True)
    blob = subprocess.run(['git', 'show', f'HEAD:{f}'], cwd=REPO, capture_output=True, check=True).stdout
    open(f'{dest}/src/{f}', 'wb').write(blob)
    same = open(f'{AM}/{f}', 'rb').read() == blob
    ok &= same
    log.append(f'src {f}: equal to the reproduced clone\'s file: {same}')
log.append(f'head {head}; RESULT ' + ('all hashes reproduced, src equal' if ok else 'FAILED'))
open(f'{W}/evidence/reproduce-{stage}.log', 'w').write('\n'.join(log) + '\n')
assert ok, log
ev = f'{dest}/evidence'
shutil.copytree(f'{W}/evidence', ev)
shutil.copytree(f'{W}/tools', f'{ev}/tools')
for d in ('ax', 'stmt', 'dup', 'probes', 'rwids'):
    if os.path.isdir(f'{REPO}/scratch/{d}'):
        shutil.copytree(f'{REPO}/scratch/{d}', f'{ev}/probe-sources/{d}')
shutil.copy(f'{REPO}/scratch/CacheProbe.lean', f'{ev}/probe-sources/CacheProbe.lean')
if os.path.isdir(f'{REPO}/scratch/seal'):
    shutil.copytree(f'{REPO}/scratch/seal', f'{ev}/rule10/probe-sources')
for x in ('SHA256SUMS',):
    if os.path.exists(f'{ev}/{x}'):
        os.remove(f'{ev}/{x}')
nev = manifest(ev, 'SHA256SUMS')
shutil.copy(f'{W}/REPORT-{stage}.md', f'{dest}/REPORT.md')
ntop = manifest(dest, 'SHA256SUMS')
print(f'{stage}: head {head}; patches {len(patches)}; src {len(OWNED)}; evidence {nev} files; '
      f'top manifest {ntop} files; reproduction OK')
