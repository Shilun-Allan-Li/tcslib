"""Package a source tip, exact commit metadata, raw evidence, and hash reproduction."""
import csv
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

phase, tip = sys.argv[1:3]
base = '01de2d8baed9113e4a099e13c5d50c81e6dbc66f'
proof = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
verification = Path('/Users/seyoonr/.codex/worktrees/derand/tcslib-exchange')
shared = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange')
destination = Path('/private/tmp/derand-worker/payloads') / phase / 'derand'
destination.mkdir(parents=True, exist_ok=False)

def git(*arguments, root=proof, env=None):
    return subprocess.check_output(['git', *arguments], cwd=root, env=env)

changed = git('diff', '--name-only', base, tip).decode().splitlines()
assert changed and all(path.startswith('TCSlib/') and path.endswith('.lean') for path in changed)
for path in changed:
    target = destination / 'src' / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(git('show', f'{tip}:{path}'))
patches = destination / 'patches'
patches.mkdir()
patch_output = git('format-patch', '--full-index', '--binary', '--no-signature',
                   '-o', str(patches), f'{base}..{tip}').decode()
patch_files = [Path(line) for line in patch_output.splitlines()]
commits = git('rev-list', '--reverse', f'{base}..{tip}').decode().splitlines()
assert len(commits) == len(patch_files)
metadata = []
for commit, patch in zip(commits, patch_files):
    fields = git('-c', 'log.showSignature=false', 'show', '-s',
                 '--format=%an%n%ae%n%aI%n%cn%n%ce%n%cI', commit).decode().splitlines()
    raw = git('cat-file', 'commit', commit)
    signing = 'none' if b'\ngpgsig ' not in raw else (
        'ssh' if b'BEGIN SSH SIGNATURE' in raw else 'openpgp-or-other')
    row = dict(zip(['author_name', 'author_email', 'author_date', 'committer_name',
                    'committer_email', 'committer_date'], fields))
    row.update(commit=commit, signing=signing, patch=patch.name)
    metadata.append(row)
with (patches / 'COMMITS.tsv').open('w', newline='') as stream:
    writer = csv.writer(stream, delimiter='\t', lineterminator='\n')
    columns = ['commit', 'author_name', 'author_email', 'author_date',
               'committer_name', 'committer_email', 'committer_date', 'signing']
    writer.writerow(columns)
    writer.writerows([row[column] for column in columns] for row in metadata)

evidence = destination / 'evidence'
evidence.mkdir()
shutil.copytree(verification / 'evidence', evidence / 'verification')
worker = evidence / 'worker'
worker.mkdir()
if phase == 'checkpoint1':
    for directory in ['scope-request', 'tools', 'probes', 'sources', 'development']:
        if (proof / 'evidence' / directory).exists():
            shutil.copytree(proof / 'evidence' / directory, worker / directory)
    worker_logs = worker / 'logs'
    worker_logs.mkdir()
    prefixes = ('checkpoint1', 'typed-host', 'lint-checkpoint1', 'preflight', 'package-pins',
                'cache', 'slots', 'courtesy-gap', 'cache-window')
    for path in (proof / 'evidence/logs').iterdir():
        if path.name.startswith(prefixes):
            if path.is_dir():
                shutil.copytree(path, worker_logs / path.name)
            else:
                shutil.copy2(path, worker_logs / path.name)
    source_seals = proof / 'evidence/seals/checkpoint1-focus-v2'
    if source_seals.exists():
        shutil.copytree(source_seals, worker / 'seals/checkpoint1-focus-v2')
else:
    for path in (proof / 'evidence').iterdir():
        if path.is_dir():
            shutil.copytree(path, worker / path.name)
        else:
            shutil.copy2(path, worker / path.name)
generators = worker / 'generators'
generators.mkdir(exist_ok=True)
for path in Path('/private/tmp/derand-worker').glob('*.py'):
    shutil.copy2(path, generators / path.name)
(evidence / 'README.md').write_text(
    '# Evidence roots\n\n'
    '`verification/` is the raw `evidence/` of the independent verification checkout at\n'
    f'`{verification}`. `worker/` is the corresponding worker-checkout evidence at\n'
    f'`{proof}`. Original log paths are unchanged inside raw records.\n\n'
    'For checkpoint 1 the worker subset contains its scope requests, prototypes, tools,\n'
    'source archives, and checkpoint/resource logs. Later consumer/host research is not\n'
    'part of the checkpoint patch. For the final, both evidence trees are included in full.\n\n'
    'No package tree or TCSlib olean is delivered. The issued wrapper and packs are under\n'
    '`verification/inputs/issued/`. Python commands used isolated `python3 -I`.\n')
repro = evidence / 'reproduction'
repro.mkdir()
scratch = Path('/private/tmp/derand-worker') / ('reproduction-' + phase)
assert not scratch.exists()
log_lines = []
def run(command, cwd=None, env=None):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log_lines.append('$ ' + ' '.join(map(str, command)) + '\n' + result.stdout +
                     f'EXIT {result.returncode}\n')
    if result.returncode:
        (repro / 'replay.log').write_text('\n'.join(log_lines))
        raise RuntimeError(command)
run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(shared), str(scratch)])
run(['git', 'checkout', '--quiet', '--detach', base], cwd=scratch)
for row, patch in zip(metadata, patch_files):
    assert row['signing'] == 'none', row
    environment = dict(os.environ, GIT_COMMITTER_NAME=row['committer_name'],
                       GIT_COMMITTER_EMAIL=row['committer_email'],
                       GIT_COMMITTER_DATE=row['committer_date'])
    run(['git', '-c', 'commit.gpgsign=false', 'am', '--quiet', str(patch)],
        cwd=scratch, env=environment)
    actual = git('rev-parse', 'HEAD', root=scratch).decode().strip()
    log_lines.append(f'EXPECTED {row["commit"]}\nACTUAL {actual}\n')
    assert actual == row['commit'], (actual, row)
(repro / 'replay.log').write_text('\n'.join(log_lines) + '\nREPRODUCTION PASS\n')
(repro / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
record = dict(phase=phase, base=base, tip=tip, source_files=changed, commits=metadata,
              reproduction='PASS', destination=str(destination))
(destination.parent / 'build-record.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
