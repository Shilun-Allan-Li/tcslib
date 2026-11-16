"""Patch series, COMMITS.tsv and a reproduction check (python3 -I).

Usage (from the fill checkout root):
    make_patches.py <base> <branch> <patches-dir> <scratch-dir> <log>
1. `git format-patch <base>..<branch> -o <patches-dir>` (the whole series; old .patch files
   in <patches-dir> are removed first).
2. `<patches-dir>/COMMITS.tsv`: one row per commit (oldest first): hash, author name, email and
   date, committer name, email and date (raw `%ad`/`%cd` with --date=raw and ISO), and signing
   (`none` when `%G?` is N and the commit object has no `gpgsig` header, else the signature
   format named by the header).
3. Reproduction: a fresh `git clone --no-checkout --shared` of this repository into
   <scratch-dir>, detached at <base>; each patch is applied with `git am` under the row's
   committer identity and date (GIT_COMMITTER_NAME/EMAIL/DATE) and
   `-c commit.gpgsign=false`; the resulting hash must equal the row's hash.
"""
import os
from pathlib import Path
import shutil
import subprocess
import sys

base, branch, pdir, scratch, log = sys.argv[1:6]
pdir, scratch = Path(pdir), Path(scratch)
pdir.mkdir(parents=True, exist_ok=True)
for old in pdir.glob('*.patch'):
    old.unlink()
run = lambda *a, **k: subprocess.run(a, check=True, capture_output=True, text=True, **k).stdout
patches = run('git', 'format-patch', f'{base}..{branch}', '-o', str(pdir)).split()
hashes = run('git', 'rev-list', '--reverse', f'{base}..{branch}').split()
assert len(patches) == len(hashes)
rows = []
fmt = '%H%x09%an%x09%ae%x09%ad%x09%cn%x09%ce%x09%cd%x09%G?'
for h in hashes:
    raw = run('git', 'log', '-1', '--date=raw', f'--format={fmt}', h).rstrip('\n').split('\t')
    iso_a = run('git', 'log', '-1', '--format=%aI', h).strip()
    iso_c = run('git', 'log', '-1', '--format=%cI', h).strip()
    obj = run('git', 'cat-file', '-p', h)
    header = obj.split('\n\n', 1)[0]
    if 'gpgsig' in header:
        sig = 'ssh' if 'BEGIN SSH SIGNATURE' in header else ('x509' if 'BEGIN SIGNED MESSAGE'
                                                            in header else 'openpgp')
    else:
        sig = 'none'
    rows.append(dict(hash=raw[0], an=raw[1], ae=raw[2], ad=raw[3], adi=iso_a, cn=raw[4],
                     ce=raw[5], cd=raw[6], cdi=iso_c, verify=raw[7], signing=sig))
with (pdir / 'COMMITS.tsv').open('w') as f:
    f.write('hash\tauthor_name\tauthor_email\tauthor_date_raw\tauthor_date_iso\t'
            'committer_name\tcommitter_email\tcommitter_date_raw\tcommitter_date_iso\tsigning\n')
    for r in rows:
        f.write(f'{r["hash"]}\t{r["an"]}\t{r["ae"]}\t{r["ad"]}\t{r["adi"]}\t{r["cn"]}\t{r["ce"]}\t'
                f'{r["cd"]}\t{r["cdi"]}\t{r["signing"]}\n')
out = [f'base {base}', f'branch {branch} -> {len(hashes)} commit(s)']
if scratch.exists():
    shutil.rmtree(scratch)
run('git', 'clone', '-q', '--no-checkout', '--shared', '.', str(scratch))
run('git', '-C', str(scratch), 'checkout', '-q', '--detach', base)
ok = True
for p, r in zip(sorted(pdir.glob('*.patch')), rows):
    env = dict(os.environ, GIT_COMMITTER_NAME=r['cn'], GIT_COMMITTER_EMAIL=r['ce'],
               GIT_COMMITTER_DATE=r['cd'])
    subprocess.run(['git', '-C', str(scratch), '-c', 'commit.gpgsign=false', 'am', '-q',
                    str(p.resolve())], check=True, env=env)
    got = run('git', '-C', str(scratch), 'rev-parse', 'HEAD').strip()
    good = got == r['hash']
    ok &= good
    out.append(f'{p.name}: am -> {got} expected {r["hash"]} {"MATCH" if good else "MISMATCH"} '
               f'(signing {r["signing"]}, %G?={r["verify"]})')
tree_ok = run('git', '-C', str(scratch), 'rev-parse', 'HEAD^{tree}').strip() == \
    run('git', 'rev-parse', f'{branch}^{{tree}}').strip()
out.append(f'final tree equals {branch}^{{tree}}: {tree_ok}')
out.append('REPRODUCTION ' + ('PASS' if ok and tree_ok else 'FAIL'))
Path(log).write_text('\n'.join(out) + '\n')
print('\n'.join(out))
shutil.rmtree(scratch)
sys.exit(0 if ok and tree_ok else 1)
