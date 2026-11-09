"""Freeze three proof-normalization corrections and resume verified prerequisites."""
from pathlib import Path
import ast
import hashlib
import json
import runpy
import subprocess

PREP = Path(__file__).resolve().parent
OUT = PREP / 'partial-r1/native-fixes-r1'
old = json.loads((OUT / 'config.json').read_text())
work = Path(old['worktree'])
modules = json.loads((OUT / 'modules.json').read_text())
header_imports = runpy.run_path(str(PREP / 'prepare_partial_native.py'))['imports']
changed = []
for row in modules:
    source = (work / (row['module'] + '.lean')).read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    names = header_imports(source.decode())
    assert [name.replace('.', '/') for name in names if name.startswith('TCSlib.')] == row['local_imports']
    assert [name for name in names if not name.startswith('TCSlib.')] == row['external_imports']
    if digest != row['source_sha256']:
        changed.append({'module': row['module'], 'before': row['source_sha256'], 'after': digest})
        row['source_sha256'] = digest
assert {row['module'] for row in changed} == {
    'TCSlib/Cryptography/Asymptotic/OneWayLemmas',
    'TCSlib/Cryptography/Asymptotic/GGMReduction',
    'TCSlib/Cryptography/ZeroKnowledge/EncodingMachines',
}
assert not (OUT / 'modules-revision02.json').exists()
(OUT / 'modules-revision02.json').write_text(json.dumps(modules, indent=2) + '\n')
config = dict(old)
config['modules_sha256'] = hashlib.sha256((OUT / 'modules-revision02.json').read_bytes()).hexdigest()
config['working_source_diff_sha256'] = hashlib.sha256(subprocess.check_output(['git', '-C', str(work), 'diff', '--binary'])).hexdigest()
config['source_revision'] = 2
config['source_changes_since_revision01'] = changed
config['revision01_config_sha256'] = hashlib.sha256((OUT / 'config.json').read_bytes()).hexdigest()
(OUT / 'config-revision02.json').write_text(json.dumps(config, indent=2) + '\n')
source = (PREP / 'run_partial_native_resume.py').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == 'b26012ad1a4f4dd32914de556e95ea20de8b734aa324ea468e8f0a94ef2c75a8'
source = source.replace("'config.json'", "'config-revision02.json'")
source = source.replace("'modules.json'", "'modules-revision02.json'")
source = source.replace('resume-01', 'resume-02')
before = "    previous_rows = [json.loads(line) for line in (OUT / 'attempts.jsonl').read_text().splitlines()]"
assert source.count(before) == 1
source = source.replace(before, '''    all_prior_rows = [json.loads(line) for line in (OUT / 'attempts.jsonl').read_text().splitlines()]
    latest = {row['module']: row for row in all_prior_rows}
    previous_rows = [row for row in latest.values() if row['passed']]
    failed_rows = [row for row in all_prior_rows if not row['passed']]
    assert len(failed_rows) == 1 and failed_rows[0]['module'] == 'TCSlib/Cryptography/Asymptotic/OneWayLemmas'
    for row in failed_rows:
        assert sha(OUT / row['log']) == row['log_sha256']''')
before = "    assert len(previous_rows) == 4 and not (OUT / 'STOP.json').exists()"
assert source.count(before) == 1
source = source.replace(before, "    assert len(previous_rows) == 88 and (OUT / 'STOP.json').exists()")
source = source.replace("'resumed_after_host_defer': True,", "'resumed_after_host_defer': True, 'historical_failed_attempts': 1, 'source_revision': 2,")
ast.parse(source)
runner = PREP / 'run_partial_native_revision02.py'
assert not runner.exists()
runner.write_text(source)
print(json.dumps({'source_revision': 2, 'changed_modules': changed,
                  'preserved_successful_prefix': 88, 'failed_attempts_preserved': 1,
                  'runner': str(runner), 'runner_sha256': hashlib.sha256(source.encode()).hexdigest(),
                  'config_sha256': hashlib.sha256((OUT / 'config-revision02.json').read_bytes()).hexdigest()}, indent=2))
