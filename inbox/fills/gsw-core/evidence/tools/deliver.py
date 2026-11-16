"""Assemble the gsw-core delivery payload (python3 -I).

usage: deliver.py ROOT DEST BASE BRANCH
  * DEST/patches/: `git format-patch BASE..BRANCH` (whole series) and COMMITS.tsv (hash, author
    name/email/date, committer name/email/date, signing);
  * DEST/src/: every file changed in BASE..BRANCH, at BRANCH, under its repository path;
  * reproduction: a scratch clone at BASE applies each patch with `git am` under the recorded
    committer identity and date, with commit.gpgsign=false; every hash must match
    (log in DEST/evidence/logs/patch-reproduction.log);
  * DEST/evidence/SHA256SUMS over every file under DEST/evidence/ except itself;
  * DEST/SHA256SUMS over every file under DEST/ except itself; then checks that the delivered
    paths equal the manifest's paths exactly (no leading `./`).
"""
import hashlib, os, shutil, subprocess, sys, tempfile
from pathlib import Path

root, dest, base, branch = sys.argv[1:5]
EXCL = sys.argv[sys.argv.index('--exclude') + 1].split(',') if '--exclude' in sys.argv else []
dest = Path(dest)


def git(*a, cwd=root, env=None):
    return subprocess.check_output(['git', *a], cwd=cwd, text=True, env=env)


# patches
pdir = dest / 'patches'
if pdir.exists():
    shutil.rmtree(pdir)
pdir.mkdir(parents=True)
git('format-patch', '-q', '--no-signature', '-o', str(pdir), f'{base}..{branch}')
fmt = '%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI%x09%G?'
rows = git('log', '--reverse', f'--format={fmt}', f'{base}..{branch}').strip().splitlines()
with open(pdir / 'COMMITS.tsv', 'w') as f:
    f.write('hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\t'
            'committer_date\tsigning\n')
    for r in rows:
        c = r.split('\t')
        c[7] = 'none' if c[7] == 'N' else f'signed({c[7]})'
        f.write('\t'.join(c) + '\n')
# src
sdir = dest / 'src'
if sdir.exists():
    shutil.rmtree(sdir)
for path in git('diff', '--name-only', f'{base}..{branch}').split():
    out = sdir / path
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(subprocess.check_output(['git', 'show', f'{branch}:{path}'], cwd=root))
# reproduction
log = dest / 'evidence/logs/patch-reproduction.log'
log.parent.mkdir(parents=True, exist_ok=True)
lines, ok = [], True
with tempfile.TemporaryDirectory(dir=os.path.expanduser('~')) as tmp:
    clone = Path(tmp) / 'repro'
    subprocess.check_call(['git', 'clone', '-q', '--no-checkout', root, str(clone)])
    git('checkout', '-q', '--detach', base, cwd=clone)
    patches = sorted(p for p in pdir.glob('*.patch'))
    for p, r in zip(patches, rows):
        c = r.split('\t')
        env = dict(os.environ, GIT_COMMITTER_NAME=c[4], GIT_COMMITTER_EMAIL=c[5],
                   GIT_COMMITTER_DATE=c[6])
        subprocess.check_call(['git', '-c', 'commit.gpgsign=false', 'am', '-q', str(p)],
                              cwd=clone, env=env)
        h = git('rev-parse', 'HEAD', cwd=clone).strip()
        lines.append(f'{p.name}: {h} expected {c[0]} {"MATCH" if h == c[0] else "MISMATCH"}')
        ok &= h == c[0]
    for path in git('diff', '--name-only', f'{base}..{branch}').split():
        same = (clone / path).read_bytes() == (sdir / path).read_bytes()
        lines.append(f'src/{path}: {"identical" if same else "DIFFERENT"} to the reproduced tree')
        ok &= same
lines.append(f'base {base}; {len(rows)} commits; scratch clone of {root}; git am with the recorded '
             'committer identity and date, commit.gpgsign=false')
lines.append('PATCH REPRODUCTION ' + ('PASS' if ok else 'FAIL'))
log.write_text('\n'.join(lines) + '\n')
print('\n'.join(lines))


def excluded(p):
    rel = p.relative_to(dest).as_posix()
    return any(rel.startswith(x) for x in EXCL)


def manifest(top, skip):
    out = []
    for p in sorted(top.rglob('*')):
        if p.is_file() and p != skip and not excluded(p):
            out.append(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(top).as_posix()}')
    skip.write_text('\n'.join(out) + '\n')
    return out


ev = dest / 'evidence'
e = manifest(ev, ev / 'SHA256SUMS')
t = manifest(dest, dest / 'SHA256SUMS')
listed = {l.split('  ', 1)[1] for l in t}
present = {p.relative_to(dest).as_posix() for p in dest.rglob('*')
           if p.is_file() and not excluded(p)} - {'SHA256SUMS'}
(Path(os.path.expanduser('~')) / 'delivery-paths.txt').write_text(
    '\n'.join(sorted(present | {'SHA256SUMS'})) + '\n')
print(f'excluded prefixes (not delivered in this phase): {EXCL}')
lead = [x for x in listed if x.startswith('./')]
print(f'evidence manifest: {len(e)} files; top manifest: {len(t)} files; '
      f'paths equal: {listed == present}; leading ./: {len(lead)}')
sys.exit(0 if ok and listed == present and not lead else 1)
