import json
import pathlib
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
log = ev / 'logs/lint-final.log'
with log.open('w') as f:
    p = subprocess.run(['python3', '-I', 'scripts/campaign_style_lint.py', 'TCSlib/Cryptography', '--check8b'], cwd=repo, stdout=f, stderr=subprocess.STDOUT)
def failures(path):
    return {tuple(line.split(None, 2)[1:]) for line in path.read_text().splitlines() if line.startswith('FAIL ')}
base = failures(ev / 'logs/lint-base.log')
final = failures(log)
result = dict(final_process_exit=p.returncode, baseline_failures=len(base), final_failures=len(final),
    new_failures=sorted(final - base), removed_failures=sorted(base - final), passed=not (final - base))
(ev / 'logs/lint-delta.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
assert result['passed']
