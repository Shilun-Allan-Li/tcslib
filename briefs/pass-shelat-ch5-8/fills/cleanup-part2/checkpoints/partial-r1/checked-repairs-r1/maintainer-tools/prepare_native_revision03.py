"""Freeze one precise owner import; keep the verified 107-module prefix."""
from pathlib import Path
import ast
import hashlib
import json
import runpy
import subprocess

PREP = Path(__file__).resolve().parent
OUT = PREP / 'partial-r1/native-fixes-r1'
config = json.loads((OUT / 'config-revision02.json').read_text())
work = Path(config['worktree'])
modules = json.loads((OUT / 'modules-revision02.json').read_text())
imports = runpy.run_path(str(PREP / 'prepare_partial_native.py'))['imports']
changed = []
for row in modules:
    raw = (work / (row['module'] + '.lean')).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    names = imports(raw.decode())
    local = [name.replace('.', '/') for name in names if name.startswith('TCSlib.')]
    external = [name for name in names if not name.startswith('TCSlib.')]
    assert external == row['external_imports']
    if digest != row['source_sha256'] or local != row['local_imports']:
        changed.append({'module': row['module'], 'old_source_sha256': row['source_sha256'],
                        'source_sha256': digest, 'old_imports': row['local_imports'], 'imports': local})
        row.update({'source_sha256': digest, 'local_imports': local})
assert len(changed) == 1 and changed[0]['module'] == 'TCSlib/Cryptography/ZeroKnowledge/EncodingMachines'
assert set(changed[0]['imports']) - set(changed[0]['old_imports']) == {'TCSlib/Complexity/Randomized/Closure'}
positions = {row['module']: index for index, row in enumerate(modules)}
assert all(positions[dep] < positions[row['module']] for row in modules for dep in row['local_imports'])
assert not (OUT / 'modules-revision03.json').exists()
(OUT / 'modules-revision03.json').write_text(json.dumps(modules, indent=2) + '\n')
config['modules_sha256'] = hashlib.sha256((OUT / 'modules-revision03.json').read_bytes()).hexdigest()
config['working_source_diff_sha256'] = hashlib.sha256(subprocess.check_output(['git', '-C', str(work), 'diff', '--binary'])).hexdigest()
config['source_revision'] = 3
config['source_changes_since_revision02'] = changed
config['revision02_config_sha256'] = hashlib.sha256((OUT / 'config-revision02.json').read_bytes()).hexdigest()
(OUT / 'config-revision03.json').write_text(json.dumps(config, indent=2) + '\n')
source = (PREP / 'run_partial_native_revision02.py').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == 'cf67fc618672a7ec382b7539d8477d5e3b0fac6385617e322c18c9a4868dd131'
source = source.replace('config-revision02.json', 'config-revision03.json')
source = source.replace('modules-revision02.json', 'modules-revision03.json')
source = source.replace('resume-02', 'resume-03')
before = "    assert len(failed_rows) == 1 and failed_rows[0]['module'] == 'TCSlib/Cryptography/Asymptotic/OneWayLemmas'"
assert source.count(before) == 1
source = source.replace(before, "    assert len(failed_rows) == 2 and {row['module'] for row in failed_rows} == {'TCSlib/Cryptography/Asymptotic/OneWayLemmas', 'TCSlib/Cryptography/ZeroKnowledge/EncodingMachines'}")
source = source.replace('len(previous_rows) == 88', 'len(previous_rows) == 108')
source = source.replace("'historical_failed_attempts': 1, 'source_revision': 2", "'historical_failed_attempts': 2, 'source_revision': 3")
before = '''        path = logs / f'{number:03d}-{module.replace("/", "_")}.attempt01.log' '''.rstrip()
assert source.count(before) == 1
source = source.replace(before, (
    "        attempt_number = 1 + sum(row['module'] == module for row in all_prior_rows)\n"
    "        path = logs / f'{number:03d}-{module.replace(\"/\", \"_\")}.attempt{attempt_number:02d}.log'"
))
ast.parse(source)
runner = PREP / 'run_partial_native_revision03.py'
assert not runner.exists()
runner.write_text(source)
print(json.dumps({'revision': 3, 'module_count': len(modules),
                  'verified_prefix_records': 108, 'historical_failures_preserved': 2,
                  'only_changed_module': changed[0], 'runner': str(runner),
                  'runner_sha256': hashlib.sha256(source.encode()).hexdigest()}, indent=2))
