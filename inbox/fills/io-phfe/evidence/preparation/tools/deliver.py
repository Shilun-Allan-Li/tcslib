"""deliver.py <delivery-dir> <base-rev> [<name>=<worktree>]... (bb1-sim-statements, lead): ADAPTED from the
bb1-machine delivery's deliver.py. Changes: several series, one per <name>=<worktree> (patches/<name>/ and
src/<name>/ from `git format-patch <base>..HEAD` of that worktree), the am-check log per series
(evidence/delivery/am-check-<name>.out), and no series at all (manifests only). Unchanged: COMMITS.tsv (hash,
author name/email/date, committer name/email/date, signing), `git am` of every patch at <base> in a scratch
clone reproducing every hash, evidence/SHA256SUMS (every file under evidence/ except itself), the top-level
SHA256SUMS (every delivered file except itself), and the path-equality check (no leading `./`).
Also: EXCLUDE (environment, comma-separated delivery-relative prefixes) leaves paths out of both manifests
(a checkpoint omits a log directory that a running process is still writing; it is not committed either)."""
import sys, os, subprocess, hashlib, shutil, tempfile
dd, base = sys.argv[1:3]
series = [a.split('=', 1) for a in sys.argv[3:]]
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
ok = True
EXCL = [x for x in os.environ.get('EXCLUDE', '').split(',') if x]
for name, repo in series:
    git = lambda *a, cwd=repo: subprocess.run(['git', *a], cwd=cwd, capture_output=True, text=True,
                                              check=True).stdout
    pd = os.path.join(dd, 'patches', name); shutil.rmtree(pd, ignore_errors=True); os.makedirs(pd)
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
    sd = os.path.join(dd, 'src', name); shutil.rmtree(sd, ignore_errors=True)
    for f in git('diff', '--name-only', f'{base}..HEAD').split():
        d = os.path.join(sd, f); os.makedirs(os.path.dirname(d), exist_ok=True)
        open(d, 'wb').write(subprocess.run(['git', 'show', f'HEAD:{f}'], cwd=repo, capture_output=True,
                                           check=True).stdout)
    tmp = tempfile.mkdtemp(prefix='am-', dir=os.environ.get('TMPDIR'))
    subprocess.run(['git', 'clone', '-q', '--shared', '--no-checkout', repo, tmp], check=True)
    git('checkout', '-q', '--detach', base, cwd=tmp)
    log = []; sok = True
    for r, p in zip(revs, sorted(x for x in os.listdir(pd) if x.endswith('.patch'))):
        row = git('log', '-1', '--format=%cn%x09%ce%x09%cI', r).strip().split('\t')
        env = dict(os.environ, GIT_COMMITTER_NAME=row[0], GIT_COMMITTER_EMAIL=row[1], GIT_COMMITTER_DATE=row[2])
        subprocess.run(['git', '-c', 'commit.gpgsign=false', 'am', '-q', '--keep-cr', os.path.join(pd, p)],
                       cwd=tmp, env=env, check=True)
        h = git('rev-parse', 'HEAD', cwd=tmp).strip()
        log.append(f"{p} {r} {h} {'REPRODUCED' if h == r else 'DIFFERENT'}"); sok &= h == r
    shutil.rmtree(tmp)
    log.append(f"REPRODUCTION {'PASS' if sok else 'FAIL'} {len(revs)} commit(s) of {name} at base {base}")
    ok &= sok
    os.makedirs(os.path.join(dd, 'evidence', 'delivery'), exist_ok=True)
    open(os.path.join(dd, 'evidence', 'delivery', f'am-check-{name}.out'), 'w').write('\n'.join(log) + '\n')
    print('\n'.join(log))
def walk(root, skip):
    out = []
    for a, _, fs in os.walk(root):
        for f in fs:
            rel = os.path.relpath(os.path.join(a, f), root)
            drel = os.path.relpath(os.path.join(a, f), dd)
            if rel != skip and not any(drel.startswith(x) for x in EXCL): out.append(rel)
    return sorted(out)
ed = os.path.join(dd, 'evidence')
ev = walk(ed, 'SHA256SUMS')
open(os.path.join(ed, 'SHA256SUMS'), 'w').write(''.join(f'{sha(os.path.join(ed, p))}  {p}\n' for p in ev))
top = walk(dd, 'SHA256SUMS')
open(os.path.join(dd, 'SHA256SUMS'), 'w').write(''.join(f'{sha(os.path.join(dd, p))}  {p}\n' for p in top))
for root, man in ((dd, 'SHA256SUMS'), (ed, 'SHA256SUMS')):
    listed = [l.split('  ', 1)[1].rstrip('\n') for l in open(os.path.join(root, man))]
    assert all(not p.startswith('./') for p in listed)
    assert sorted(listed) == walk(root, man), ('manifest mismatch', root)
print('manifests: top', len(top), 'evidence', len(ev), 'paths equal: True')
sys.exit(0 if ok else 1)
