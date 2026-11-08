"""Run reviewed repository static lints on the eight local repair files."""
from pathlib import Path
import collections
import hashlib
import json
import re
import runpy
import subprocess

PREP = Path(__file__).resolve().parent
PART = PREP / 'partial-r1'
WORK = Path('/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4')
BEFORE = PART / 'payload/src'
OUT = PART / 'local-style-delta'
files = subprocess.check_output(['git', '-C', str(WORK), 'diff', '--name-only'], text=True).splitlines()
assert len(files) == 8 and all(name.endswith('.lean') for name in files)
assert not OUT.exists()
OUT.mkdir()
assert all(not (WORK / name).with_suffix('').is_dir() for name in files)
repo = runpy.run_path(str(WORK / 'scripts/style_lint.py'))
campaign = runpy.run_path(str(WORK / 'scripts/campaign_style_lint.py'))
repo_globals = repo['lint'].__globals__
campaign_globals = campaign['check_file'].__globals__


def normalize(message):
    message = re.sub(r':\d+:', ':<line>:', message)
    message = re.sub(r'line \d+:', 'line <line>:', message)
    message = re.sub(r'\b\d+ lines', '<count> lines', message)
    return message


reports = {}
for label, root in [('received', BEFORE), ('local', WORK)]:
    repo_globals['ROOT'] = root
    repo_rows = [message for name in files for message in repo['lint'](root / name)]
    (OUT / (label + '-repository.log')).write_text('\n'.join(repo_rows) + '\n')
    rows = {'repository': repo_rows, 'line_counts': {name: len((root / name).read_text().splitlines()) for name in files}}
    for check8b in [False, True]:
        campaign_globals['ROOT'] = root
        campaign_globals['CHECK8B'] = check8b
        campaign_globals['findings'] = []
        for name in files:
            campaign['check_file'](root / name)
        findings = list(campaign_globals['findings'])
        key = 'campaign-check8b' if check8b else 'campaign-plain'
        rows[key] = findings
        (OUT / (label + '-' + key + '.log')).write_text(
            '\n'.join(f'{level}  {path}  {message}' for level, path, message in findings) + '\n')
    reports[label] = rows
deltas = {}
for kind in ['repository', 'campaign-plain', 'campaign-check8b']:
    def identities(label):
        if kind == 'repository':
            return collections.Counter(normalize(message) for message in reports[label][kind])
        return collections.Counter((level, path, normalize(message))
                                   for level, path, message in reports[label][kind] if level != 'INFO')
    old = identities('received')
    new = identities('local')
    deltas[kind] = {'added': list((new-old).elements()), 'removed': list((old-new).elements()),
                    'before_count': sum(old.values()), 'after_count': sum(new.values())}
result = {'comparison': 'local eight repairs against immutable received partial source',
          'files': files, 'normalization': 'Ignore source line shifts and numeric size counts; preserve finding category/name/path/level.',
          'tool_sha256': {name: hashlib.sha256((WORK/'scripts'/name).read_bytes()).hexdigest()
                          for name in ['style_lint.py', 'campaign_style_lint.py']},
          'reports': reports, 'deltas': deltas,
          'zero_new_normalized_findings': all(not value['added'] for value in deltas.values()),
          'limit': 'Static local-delta checks only; inherited findings and standing size exceptions retained.'}
(OUT / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'zero_new_normalized_findings': result['zero_new_normalized_findings'], 'deltas': deltas}, indent=2))
