"""deliver.py <repo> <base-rev> <delivery-dir> (fill bb1-machine, Claude lead): assemble the payload's
`patches/` (git format-patch <base>..HEAD, plus COMMITS.tsv: hash, author name/email/date, committer
name/email/date, signing), `src/` (the files changed in <base>..HEAD at HEAD, under their repository
paths), `evidence/SHA256SUMS` (every file under evidence/ except itself) and the top-level `SHA256SUMS`
(every delivered file except itself); then check that the delivered paths equal the manifests' paths
(no leading `./`) and that `git am` of the patches at <base> in a scratch clone reproduces every hash."""
import sys, os, subprocess, hashlib, shutil, tempfile
repo, base, dd = sys.argv[1:4]
git = lambda *a, cwd=repo: subprocess.run(['git', *a], cwd=cwd, capture_output=True, text=True, check=True).stdout
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
pd = os.path.join(dd, 'patches'); shutil.rmtree(pd, ignore_errors=True); os.makedirs(pd)
git('format-patch', '-q', '--no-signature', '-o', pd, f'{base}..HEAD')
revs = git('rev-list', '--reverse', f'{base}..HEAD').split()
rows = ['hash\tauthor_name\tauthor_email\tauthor_date\tcommitter_name\tcommitter_email\tcommitter_date\tsigning']
for r in revs:
    f = git('log', '-1', '--format=%H%x09%an%x09%ae%x09%aI%x09%cn%x09%ce%x09%cI', r).strip()
    raw = git('cat-file', 'commit', r)
    sig = 'none'
    if 'gpgsig ' in raw:
        sig = 'ssh' if 'BEGIN SSH SIGNATURE' in raw else 'gpg'
    rows.append(f + '\t' + sig)
open(os.path.join(pd, 'COMMITS.tsv'), 'w').write('\n'.join(rows) + '\n')
sd = os.path.join(dd, 'src'); shutil.rmtree(sd, ignore_errors=True)
for f in git('diff', '--name-only', f'{base}..HEAD').split():
    d = os.path.join(sd, f); os.makedirs(os.path.dirname(d), exist_ok=True)
    open(d, 'wb').write(subprocess.run(['git', 'show', f'HEAD:{f}'], cwd=repo, capture_output=True, check=True).stdout)
# reproduction in a scratch clone
tmp = tempfile.mkdtemp(prefix='am-', dir=os.environ.get('TMPDIR'))
subprocess.run(['git', 'clone', '-q', '--shared', '--no-checkout', repo, tmp], check=True)
git('checkout', '-q', '--detach', base, cwd=tmp)
ok = True
log = []
for r, p in zip(revs, sorted(x for x in os.listdir(pd) if x.endswith('.patch'))):
    row = git('log', '-1', '--format=%cn%x09%ce%x09%cI', r).strip().split('\t')
    env = dict(os.environ, GIT_COMMITTER_NAME=row[0], GIT_COMMITTER_EMAIL=row[1], GIT_COMMITTER_DATE=row[2])
    subprocess.run(['git', '-c', 'commit.gpgsign=false', 'am', '-q', '--keep-cr', os.path.join(pd, p)],
                   cwd=tmp, env=env, check=True)
    h = git('rev-parse', 'HEAD', cwd=tmp).strip()
    log.append(f"{p} {r} {h} {'REPRODUCED' if h == r else 'DIFFERENT'}"); ok &= h == r
shutil.rmtree(tmp)
log.append(f"REPRODUCTION {'PASS' if ok else 'FAIL'} {len(revs)} commit(s) at base {base}")
os.makedirs(os.path.join(dd, 'evidence', 'delivery'), exist_ok=True)
open(os.path.join(dd, 'evidence', 'delivery', 'am-check.out'), 'w').write('\n'.join(log) + '\n')
print('\n'.join(log))
def walk(root, skip):
    out = []
    for a, _, fs in os.walk(root):
        for f in fs:
            rel = os.path.relpath(os.path.join(a, f), root)
            if rel != skip: out.append(rel)
    return sorted(out)
ed = os.path.join(dd, 'evidence')
ev = walk(ed, 'SHA256SUMS')
open(os.path.join(ed, 'SHA256SUMS'), 'w').write(''.join(f'{sha(os.path.join(ed, p))}  {p}\n' for p in ev))
top = walk(dd, 'SHA256SUMS')
open(os.path.join(dd, 'SHA256SUMS'), 'w').write(''.join(f'{sha(os.path.join(dd, p))}  {p}\n' for p in top))
# path equality
for root, man in ((dd, 'SHA256SUMS'), (ed, 'SHA256SUMS')):
    listed = [l.split('  ', 1)[1].rstrip('\n') for l in open(os.path.join(root, man))]
    assert all(not p.startswith('./') for p in listed)
    assert sorted(listed) == walk(root, man), ('manifest mismatch', root)
print('manifests: top', len(top), 'evidence', len(ev), 'paths equal: True')
sys.exit(0 if ok else 1)
