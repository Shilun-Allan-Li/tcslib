"""Reconcile serial-check source/object fingerprints and prerequisite freshness.

Usage: python3 -I reconcile.py <evidence-run-dir> <new-label>
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

r = Path.cwd()
e, label = Path(sys.argv[1]), sys.argv[2]
order = (r / '.lake/ps-maintainer/gate06/order-current.txt').read_text().splitlines()
members = set(order)
latest = {}
for log in (e / 'logs').glob('*/replay.jsonl'):
    for line in log.read_text().splitlines():
        v = json.loads(line)
        if v['module'] in members and v['rc'] == 0 and (v['module'] not in latest or v['end'] > latest[v['module']]['end']):
            latest[v['module']] = {**v, 'attempt': log.parent.name}
assert set(latest) == members
deps = {m: [d.replace('.', '/') for d in re.findall(r'(?m)^import\s+(TCSlib\.\S+)', (r / (m + '.lean')).read_text())] for m in order}
assert all(set(ds) <= members for ds in deps.values())
tree = Path(json.loads((e / 'setup-summary.json').read_text())['olean_tree'])
reasons, manifest = {}, {}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for m in order:
    v, why = latest[m], []
    src, obj = r / (m + '.lean'), tree / (m + '.olean')
    if sha(src) != v['source_sha256']:
        why.append('source changed')
    if not obj.is_file() or sha(obj) != v['object_sha256']:
        why.append('object absent or differs')
    if not v['source_unchanged_during_check'] or not v['fresh_nonempty_object']:
        why.append('invalid source/object check')
    for d in deps[m]:
        if d in reasons:
            why.append('dirty import ' + d)
        elif latest[d]['end'] > v['start']:
            why.append('import rebuilt later ' + d)
    if why:
        reasons[m] = why
    manifest[m] = {**v, 'import_object_hashes': {d: latest[d]['object_sha256'] for d in deps[m]}}
output = e / (label + '.json')
assert not output.exists()
output.write_text(json.dumps({'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), 'modules': len(order), 'stale_modules': len(reasons), 'reasons': reasons, 'manifest': manifest, 'limit': 'Current source bytes and object bytes match their latest successful checks when stale_modules is zero; all recorded direct TCSlib prerequisites were checked before consumers. Mathlib/toolchain pins are covered by setup evidence. TCSlib root export module is not part of this 467-module union.'}, indent=2) + '\n')
(e / (label + '-order.txt')).write_text('\n'.join(m for m in order if m in reasons) + ('\n' if reasons else ''))
(e / 'reconcile.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), 'modules': len(order), 'stale_modules': len(reasons), 'first': list(reasons)[:8]}))
