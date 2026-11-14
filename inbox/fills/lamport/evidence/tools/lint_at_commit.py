"""Lint a frozen source-only archive without including uncommitted future helpers.

Use python3 -I. No checkout, cache or olean tree is created; no Lean is invoked.
"""
import argparse
import io
import json
from pathlib import Path
import subprocess
import tarfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--evidence', required=True)
parser.add_argument('--commit', required=True)
parser.add_argument('--phase', required=True)
args = parser.parse_args()
root, evidence = Path(args.root), Path(args.evidence)
export = root.parent / ('source-audit-' + args.phase)
export.mkdir(exist_ok=False)
raw = subprocess.check_output(['git', '-C', str(root), 'archive', args.commit,
                               'TCSlib', 'scripts/campaign_style_lint.py'])
with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
    archive.extractall(export, filter='data')
command = ['python3', '-I', 'scripts/campaign_style_lint.py',
           'TCSlib/Cryptography', '--check8b']
result = subprocess.run(command, cwd=export, capture_output=True, text=True)
log = evidence / 'logs' / ('style-' + args.phase + '-delivered-tree.log')
comparison = evidence / 'logs' / ('lint-' + args.phase + '-comparison.json')
assert not log.exists() and not comparison.exists()
log.write_text('$ ' + ' '.join(command) + '\n' + result.stdout + result.stderr +
               '\nexit=' + str(result.returncode) + '\n')


def failures(text):
    return {line for line in text.splitlines() if line.lstrip().startswith('FAIL')}


baseline = failures((evidence / 'logs/style-base.log').read_text())
current = failures(result.stdout)
data = dict(commit=args.commit, export=str(export), exit=result.returncode,
            baseline_count=len(baseline), current_count=len(current),
            new=sorted(current - baseline), removed=sorted(baseline - current))
comparison.write_text(json.dumps(data, indent=2) + '\n')
print(json.dumps(data, indent=2))
assert not data['new'], data['new']
