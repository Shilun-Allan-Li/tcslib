"""Prepare two-module forwarding prechecks at a committed revision; no Lean execution."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OWNERS = ['TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler',
          'TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame']
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('action', choices=['collect', 'seals'])
parser.add_argument('--repo', type=Path, default=Path('/private/tmp/hash-sign-fill/repo'))
parser.add_argument('--rev', default='15f43fd73b9f466263312403896953ca0ece0017')
parser.add_argument('--out', type=Path, default=ROOT / 'rule10/precheck-forward')
parser.add_argument('--collector-log', type=Path)
args = parser.parse_args()
repo, out = args.repo.resolve(), args.out.resolve()
sub = '.lake/hash-sign-rule10/precheck-forward'
out.mkdir(parents=True, exist_ok=True)
rev = subprocess.check_output(['git', '--no-optional-locks', '-C', str(repo), 'rev-parse', args.rev], text=True).strip()
sources = {}
for owner in OWNERS:
    path = owner.replace('.', '/') + '.lean'
    raw = subprocess.check_output(['git', '--no-optional-locks', '-C', str(repo), 'show', rev + ':' + path])
    if (repo / path).read_bytes() != raw:
        raise RuntimeError('precheck working source differs from committed bytes: ' + path)
    sources[path] = hashlib.sha256(raw).hexdigest()
versions = out / 'tool-versions'
versions.mkdir(exist_ok=True)
for source in [Path(__file__), HERE / 'mkcollect.py', HERE / 'mkseals_ab.py', HERE / 'NmCollect.template.lean',
               HERE / 'run_probe.py', ROOT / 'tools/check_module.py', *(HERE / 'archived-gate10-tools').glob('*.py')]:
    raw = source.read_bytes()
    (versions / (source.stem + '-' + hashlib.sha256(raw).hexdigest() + source.suffix)).write_bytes(raw)
(out / 'owners.txt').write_text('\n'.join(OWNERS) + '\n')
if args.action == 'collect':
    probe = repo / (sub + '/Collect.lean')
    probe.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run([sys.executable, '-I', str(HERE / 'mkcollect.py'), str(HERE / 'NmCollect.template.lean'),
                    str(out / 'owners.txt'), 'Hash-sign preliminary forwarding collector', str(probe)], check=True)
    (out / 'Collect.lean').write_bytes(probe.read_bytes())
    (out / 'preparation.json').write_text(json.dumps({'rev': rev, 'owners': OWNERS, 'source_sha256': sources,
         'collector_module': sub + '/Collect', 'collector_sha256': hashlib.sha256(probe.read_bytes()).hexdigest(),
         'imports_facade': False, 'controls': 'Not rerun; baseline paired controls already complete.'}, indent=2) + '\n')
    print('collector_module:', sub + '/Collect')
else:
    if not args.collector_log:
        raise RuntimeError('successful --collector-log required')
    text = args.collector_log.read_text()
    if not text.rstrip().endswith('exit: 0'):
        raise RuntimeError('collector did not complete successfully')
    import os
    for letter in ['B', 'A']:
        env = dict(os.environ, SEAL_CHUNK='500')
        if letter == 'B': env['SEAL_EVAL'] = '1'
        else: env.pop('SEAL_EVAL', None)
        subprocess.run([sys.executable, '-I', str(HERE / 'mkseals_ab.py'), str(HERE / 'archived-gate10-tools'),
            str(args.collector_log), str(repo), rev, str(out / ('seal-' + letter)), sub, 'Seal' + letter + '_', *OWNERS],
            env=env, check=True)
