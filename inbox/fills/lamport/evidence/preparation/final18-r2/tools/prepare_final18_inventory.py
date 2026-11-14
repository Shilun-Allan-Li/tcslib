"""Prepare final eighteen one-target Rule-10 inventories; never invokes Lean.

All generated phases are fresh, raw preparation logs are written in place, and the
preparation tool/version, pinned sources, base-absence diagnostics and queue are retained.
"""
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root, evidence = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
base = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
revision = '47ced271090f45918645c842cd358c5079092754'
prep = evidence / 'preparation/final18-r2'
logs = evidence / 'logs/final18-preparation-r2'
assert not prep.exists() and not logs.exists(), 'fresh preparation attempt required'
prep.mkdir(parents=True)
logs.mkdir(parents=True)
(prep / 'tools').mkdir()
tool = evidence / 'preparation/final18-r1/tools/prepare_seals.py'
frozen_tool = prep / 'tools/prepare_seals.py'
frozen_tool.write_bytes(tool.read_bytes())
(prep / 'tools/prepare_final18_inventory.py').write_bytes(Path(__file__).read_bytes())


def git(*args):
    return subprocess.run(['git', '--no-optional-locks', '-C', str(root), *args], capture_output=True)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def save_json(path, obj):
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')


assert git('rev-parse', 'HEAD').stdout.decode().strip() == revision
changed = git('diff', '--name-only', base, revision, '--', '*.lean').stdout.decode().splitlines()
prefix = 'TCSlib/Cryptography/Authentication/Signatures/Lamport/'
helpers = sorted(path for path in changed if path.startswith(prefix))
assert len(changed) == 18 and len(helpers) == 16
assert set(changed) == set(helpers) | {'TCSlib/Cryptography/Authentication.lean',
    'TCSlib/Cryptography/Authentication/Signatures/Lamport.lean'}
modules = [path.removesuffix('.lean') for path in changed]
sweep_audit_path = evidence / 'inputs/final-r2-order-audit.json'
sweep_audit = json.loads(sweep_audit_path.read_text())
sweep_order = (evidence / 'inputs/final-r2-order.txt').read_text().splitlines()
assert len(sweep_order) == 177
targets = [m for m in sweep_order if m in set(modules)]
assert len(targets) == 18

pinned, doc_audit = {}, []
for path in changed:
    p = git('show', revision + ':' + path)
    assert p.returncode == 0
    raw = p.stdout
    assert (root / path).read_bytes() == raw, 'current source differs from frozen final revision: ' + path
    module = path.removesuffix('.lean')
    assert sweep_audit['source_sha256'][module] == sha(raw)
    pinned[path] = raw
    dest = prep / 'sources' / path
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(raw)
    if path not in helpers:
        continue
    text, lines = raw.decode(), raw.decode().splitlines()
    fields = ['Copyright', 'import ', 'set_option maxHeartbeats 0',
              'set_option relaxedAutoImplicit false', 'set_option autoImplicit false',
              '# ', '## Main definitions', '## Main results', '## References']
    missing = [field for field in fields if field not in text]
    decls = [(i, line) for i, line in enumerate(lines, 1)
             if re.match(r'^(?:noncomputable )?(?:def|abbrev|theorem|lemma)\b', line)]
    undocumented = [(i, line) for i, line in decls if not '\n'.join(lines[:i - 1]).rstrip().endswith('-/')]
    assert not missing and not undocumented and len(lines) < 1000, path
    doc_audit.append(dict(path=path, sha256=sha(raw), lines=len(lines),
        missing_header_fields=missing, undocumented_declarations=undocumented, declarations=decls))
save_json(prep / 'helper-source-audit.json', doc_audit)

absence = []
with (logs / 'issue-base-helper-absence.log').open('w') as log:
    for path in helpers:
        command = ['git', '--no-optional-locks', '-C', str(root), 'cat-file', '-e', base + ':' + path]
        log.write('$ ' + ' '.join(command) + '\n')
        log.flush()
        p = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        log.write(f'EXIT {p.returncode}\n\n')
        assert p.returncode != 0, 'new helper unexpectedly present at issue base: ' + path
        absence.append(dict(path=path, revision=base, status='ABSENT', exit=p.returncode,
                            base_compile='NOT_APPLICABLE; no source existed'))
save_json(prep / 'issue-base-helper-absence.json', absence)

roots = set()
for module in sweep_order:
    raw = git('show', revision + ':' + module + '.lean')
    assert raw.returncode == 0
    assert sha(raw.stdout) == sweep_audit['source_sha256'][module]
    for line in raw.stdout.decode().splitlines():
        if line.startswith('import Mathlib.'):
            roots.update(line.split()[1:])
issued_roots = set((evidence / 'inputs/roots.txt').read_text().splitlines())
assert roots == issued_roots and len(roots) == 82
save_json(prep / 'mathlib-root-audit.json', dict(compiler_run=False, modules=177,
    roots=sorted(roots), issued_roots=sorted(issued_roots), root_count=82, new_roots=[]))

plan = []
for target in targets:
    if target == 'TCSlib/Cryptography/Authentication':
        suffix = 'Auth'
    elif target == 'TCSlib/Cryptography/Authentication/Signatures/Lamport':
        suffix = 'Main'
    else:
        suffix = target.split('/')[-1]
    phase = 'FinalR2' + suffix
    plan.append(dict(root=str(root), evidence=str(evidence), revision=revision,
        phase=phase, target=target.replace('/', '.'),
        phase_directory=str(evidence / 'seals' / phase),
        inventory_order=str(evidence / 'seals' / phase / 'inventory-order.txt'),
        snapshot_module=f'LamportEvidence/Seals/{phase}/Snapshot0',
        snapshot_attempt=phase + 'Snapshot01',
        collector_module=f'LamportEvidence/Seals/{phase}/Inventory',
        collector_attempt=phase + 'Inventory01',
        collector_raw_log=str(evidence / 'logs/helper-checks' / ('Inventory-' + phase + 'Inventory01.log')),
        preparation_log=str(logs / (phase + '.log')),
        requires_final_canonical_products=True, native_status='NOT_RUN'))
save_json(prep / 'plan.json', dict(revision=revision, count=18,
    requires_full_final_sweep_complete=True, prepare_tool_sha256=sha(frozen_tool.read_bytes()), prepare_tool_origin=str(tool), records=plan))

completed = []
for record in plan:
    command = ['python3', '-I', str(frozen_tool), 'inventory', '--root', str(root),
        '--evidence', str(evidence), '--phase', record['phase'], '--revision', revision, record['target']]
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print('PREPARING ' + record['phase'], flush=True)
    with Path(record['preparation_log']).open('w') as log:
        log.write(f'START {start}\nCOMMAND {command!r}\n')
        log.flush()
        p = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        log.write(f'END {end}\nEXIT {p.returncode}\n')
    row = dict(record, preparation_start=start, preparation_end=end, preparation_exit=p.returncode)
    with (logs / 'results.jsonl').open('a') as log:
        log.write(json.dumps(row) + '\n')
    assert p.returncode == 0, record['phase']
    manifest_path = Path(record['phase_directory']) / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    assert len(manifest['records']) == 1
    own = manifest['records'][0]
    assert own['revision'] == revision and own['source_sha256'] == sha(pinned[record['target'].replace('.', '/') + '.lean'])
    row.update(manifest=str(manifest_path), manifest_sha256=sha(manifest_path.read_bytes()),
               closure_modules=len(own['closure']), source_sha256=own['source_sha256'],
               collector_source_sha256=manifest['inventory_sha256'])
    completed.append(row)
    print('PREPARED ' + record['phase'] + '; closure=' + str(row['closure_modules']), flush=True)
save_json(prep / 'queue.json', dict(revision=revision, count=18,
    status='ALL_INVENTORIES_PREPARED_NATIVE_NOT_RUN',
    requires_full_final_sweep_complete=True, prepare_tool_sha256=sha(frozen_tool.read_bytes()),
    prepare_tool_origin=str(tool), records=completed))
print(prep / 'queue.json', flush=True)
