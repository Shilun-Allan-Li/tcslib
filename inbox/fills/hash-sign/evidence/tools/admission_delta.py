import json
import pathlib
import re
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
baseline = set()
for line in (ev / 'inputs/base-sorries.txt').read_text().splitlines():
    if line.startswith('TOTAL') or not line:
        continue
    module, _, names = line.split(': ', 2)
    if not module.startswith('TCSlib/'):
        module = 'TCSlib/Complexity/' + module
    for name in names.split(', '):
        baseline.add((module, name.split('.')[-1]))
warnings = []
pattern = re.compile(r'^([^:\n]+)\.lean:(\d+):\d+: warning: declaration uses .sorry.', re.M)
decl = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+([^\s:(]+)')
selection = ev / 'logs/final-sweep-results.jsonl'
if selection.exists():
    logs = [ev / json.loads(s)['log'] for s in selection.read_text().splitlines()]
else:
    logs = sorted((ev / 'logs/sweep').glob('*.log'))
for log in logs:
    for module, line in pattern.findall(log.read_text()):
        lines = (repo / (module + '.lean')).read_text().splitlines()
        name = None
        for source in lines[:int(line)]:
            m = decl.match(source)
            if m:
                name = m[1].split('.')[-1]
        if name is None:
            raise SystemExit('No source declaration at ' + module + ':' + line)
        warnings.append((module, name))
actual = set(warnings)
target = ('TCSlib/Cryptography/Authentication/Signatures/HashAndSign', 'hashAndSign_oneTimeSecure')
report = dict(source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
    base_count=len(baseline), final_count=len(actual), warning_count=len(warnings),
    removed=sorted(baseline - actual), added=sorted(actual - baseline),
    actual=sorted(actual), passed=actual == baseline - {target})
(ev / 'logs/admission-delta.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
raise SystemExit(not report['passed'])
