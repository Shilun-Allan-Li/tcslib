"""Root-reviewed, serial proposal integration; stop immediately on any failed action."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

r = Path.cwd()
g = r / '.lake/ps-maintainer/gate06'
helper = g / 'repairs/apply_exact_proposal.py'
assert hashlib.sha256(helper.read_bytes()).hexdigest() == '125c58457708317015dd0cce9695b83521644bdbbda3841e5cc855fc63923951'
tasks_path = Path(sys.argv[1])
tasks = json.loads(tasks_path.read_text())
assert isinstance(tasks, list) and tasks
e = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/repair-r1/native')
for task in tasks:
    module, label = task['module'], task['label']
    assert module.startswith('TCSlib/') and '..' not in module
    for name in task['patches']:
        patch = g / 'repairs' / name
        assert patch.parent == g / 'repairs' and patch.is_file()
        prefix = g / 'repairs' / ('applied-' + label + '-' + patch.stem)
        subprocess.run(['python3', '-I', str(helper), str(patch), '--out-prefix', str(prefix), '--apply'], cwd=r, check=True)
    subprocess.run(['python3', '-I', str(g/'check_probe_v2.py'), str(e), module, label], cwd=r, check=True)
    result = json.loads((e/(label+'.json')).read_text())
    assert result['rc'] == 0 and result['source_unchanged'] and result['fresh_nonempty_object'] and result['error_diagnostics'] == 0
    print('CHECKED REPAIR', module, result['source_sha256'], flush=True)
