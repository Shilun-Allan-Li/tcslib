"""Reconcile serial-check source/object fingerprints and prerequisite freshness.

Usage: python3 -I reconcile_final.py <evidence-run-dir> <new-label> <final-order-path>
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

r = Path.cwd()
e, label = Path(sys.argv[1]), sys.argv[2]
order_path = Path(sys.argv[3])
order = order_path.read_text().splitlines()
sys.dont_write_bytecode = True
header_tool = r/'.lake/ps-maintainer/gate06/build_seals.py'
assert hashlib.sha256(header_tool.read_bytes()).hexdigest() == 'fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a'
spec = importlib.util.spec_from_file_location('final_reconcile_headers', header_tool)
bs = importlib.util.module_from_spec(spec); spec.loader.exec_module(bs)
members = set(order)
latest = {}
for log in (e / 'logs').glob('*/replay.jsonl'):
    for line in log.read_text().splitlines():
        v = json.loads(line)
        if v['module'] in members and v['rc'] == 0 and (v['module'] not in latest or v['end'] > latest[v['module']]['end']):
            latest[v['module']] = {**v, 'attempt': log.parent.name}
assert set(latest) == members
deps = {m: [d.replace('.', '/') for d in bs.header((r / (m + '.lean')).read_bytes())['imports'] if d.startswith('TCSlib.')] for m in order}
positions = {m:i for i,m in enumerate(order)}
assert all(positions[d]<positions[m] for m,ds in deps.items() for d in ds)
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
output.write_text(json.dumps({'native_order_path':str(order_path),'native_order_sha256':hashlib.sha256(order_path.read_bytes()).hexdigest(),'header_tool_sha256':hashlib.sha256(header_tool.read_bytes()).hexdigest(),'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), 'modules': len(order), 'stale_modules': len(reasons), 'reasons': reasons, 'manifest': manifest, 'limit': 'Current source bytes and object bytes match their latest successful checks when stale_modules is zero; all recorded direct TCSlib prerequisites were checked before consumers. Mathlib/toolchain pins are covered by setup evidence. TCSlib root export module is not part of the current derived native union.'}, indent=2) + '\n')
(e / (label + '-order.txt')).write_text('\n'.join(m for m in order if m in reasons) + ('\n' if reasons else ''))
saved_tool=e/'reconcile_final.py'
if saved_tool.exists(): assert saved_tool.read_bytes()==Path(__file__).read_bytes()
else: saved_tool.write_bytes(Path(__file__).read_bytes())
print(json.dumps({'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(), 'modules': len(order), 'stale_modules': len(reasons), 'first': list(reasons)[:8]}))
