#!/usr/bin/env python3
"""Deliver only the authorized unit path from its dedicated worktree, without force."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

p = argparse.ArgumentParser()
p.add_argument('payload')
p.add_argument('--stage', choices=['checkpoint4', 'final'], required=True)
p.add_argument('--replace-unpublished', action='store_true')
a = p.parse_args()
payload = Path(a.payload).resolve()
delivery = Path('/Users/seyoonr/.codex/worktrees/sc-yao-delivery/tcslib-exchange')
unit = 'inbox/fills/sc-yao'

def git(*args):
    return subprocess.check_output(['git', '-C', str(delivery), *args], text=True).strip()

def verify(scope):
    manifest = scope / 'SHA256SUMS'
    rows = {}
    for line in manifest.read_text().splitlines():
        digest, name = line.split(None, 1)
        assert not name.startswith('./') and not Path(name).is_absolute()
        assert '..' not in Path(name).parts and name not in rows
        rows[name] = digest
    actual = {p.relative_to(scope).as_posix() for p in scope.rglob('*')
              if p.is_file() and p != manifest}
    assert actual == set(rows), (actual - set(rows), set(rows) - actual)
    for name, digest in rows.items():
        assert hashlib.sha256((scope / name).read_bytes()).hexdigest() == digest, name
    return len(rows)

assert git('branch', '--show-current') == 'codex/sc-yao-delivery'
assert not git('status', '--porcelain'), 'Delivery worktree must be clean'
counts = dict(top=verify(payload), evidence=verify(payload / 'evidence'))
assert all(p.stat().st_size < 100_000_000 for p in payload.rglob('*') if p.is_file())
backup = None
if a.replace_unpublished:
    assert a.stage == 'checkpoint4'
    assert git('show', '-s', '--format=%s') == 'fill sc-yao: checkpoint 4'
    assert git('rev-list', '--count', 'origin/exchange/pass-shelat-ch5-8..HEAD') == '1'
    pending = git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').splitlines()
    assert pending and all(n.startswith(unit + '/') for n in pending)
    backup = 'codex/sc-yao-checkpoint4-unpublished-oversize'
    subprocess.run(['git', '-C', str(delivery), 'branch', backup, 'HEAD'], check=True)
dest = delivery / unit
assert dest.parent == delivery / 'inbox/fills'
shutil.rmtree(dest)
shutil.copytree(payload, dest)
assert verify(dest) == counts['top'] and verify(dest / 'evidence') == counts['evidence']
subprocess.run(['git', '-C', str(delivery), 'add', '--all', '--', unit], check=True)
staged = git('diff', '--cached', '--name-only').splitlines()
assert staged and all(n.startswith(unit + '/') for n in staged), staged
message = 'fill sc-yao: final' if a.stage == 'final' else 'fill sc-yao: checkpoint 4'
logpath = Path('/private/tmp') / ('sc-yao-' + a.stage + '-delivery.log')
with logpath.open('w') as log:
    command = ['git', '-C', str(delivery), '-c', 'commit.gpgsign=false', 'commit']
    command += ['--amend', '--no-edit'] if a.replace_unpublished else ['-m', message]
    subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
    subprocess.run(['git', '-C', str(delivery), 'pull', '--rebase', 'origin',
                    'exchange/pass-shelat-ch5-8'], stdout=log,
                   stderr=subprocess.STDOUT, check=True)
    commit = git('rev-parse', 'HEAD')
    files = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).splitlines()
    assert files and all(n.startswith(unit + '/') for n in files), files
    assert git('show', '-s', '--format=%G?', commit) == 'N'
    # Rebase must preserve the payload exactly, including every manifest path and hash.
    assert verify(dest) == counts['top'] and verify(dest / 'evidence') == counts['evidence']
    result = subprocess.run(['git', '-C', str(delivery), 'push', 'origin',
                             'HEAD:exchange/pass-shelat-ch5-8'], stdout=log,
                            stderr=subprocess.STDOUT)
record = dict(commit=commit, payload=str(payload), counts=counts, pushed=result.returncode == 0,
              unpublished_backup_ref=backup,
              push_exit=result.returncode, log=str(logpath), scoped_files=len(files),
              clean=not git('status', '--porcelain'))
out = Path('evidence') / (a.stage + '-delivery.json')
assert not out.exists(), out
out.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
if result.returncode:
    print('PUSH REFUSED: commit retained; no force or retry attempted.')
    raise SystemExit(result.returncode)
