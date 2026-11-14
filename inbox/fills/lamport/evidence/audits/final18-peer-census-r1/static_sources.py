"""Independent static audit of the frozen final18 source/closure manifests.

Run as python3 -I. No Lean, Lake, phase preparation, source edits or olean
writes. Native inventory/seal results are deliberately not asserted here.
"""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
EVIDENCE = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
HERE = Path(__file__).parent
QUEUE = EVIDENCE / 'preparation/final18-r2/queue.json'
REVISION = '47ced271090f45918645c842cd358c5079092754'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


cache = {}


def blob(module):
    if module not in cache:
        cache[module] = subprocess.check_output(
            ['git', '--no-optional-locks', '-C', str(ROOT), 'show',
             REVISION + ':' + module.replace('.', '/') + '.lean'])
    return cache[module]


def imports(module):
    result = []
    for line in blob(module).decode().splitlines():
        if line.startswith('import '):
            words = line.split()[1:]
            if '--' in words:
                words = words[:words.index('--')]
            result.extend(word for word in words if word.startswith('TCSlib.'))
    return result


def closure(module):
    result = set()

    def visit(current):
        for child in imports(current):
            if child not in result:
                result.add(child)
                visit(child)

    visit(module)
    if module in result:
        raise RuntimeError('cyclic frozen import graph at ' + module)
    return sorted(result)


queue_raw = QUEUE.read_bytes()
queue = json.loads(queue_raw)
assert queue['revision'] == REVISION and queue['count'] == 18
rows = []
for record in queue['records']:
    manifest_path = Path(record['manifest'])
    raw_manifest = manifest_path.read_bytes()
    manifest = json.loads(raw_manifest)
    assert len(manifest['records']) == 1
    own = manifest['records'][0]
    module = record['target']
    expected = closure(module)
    phase_dir = Path(record['phase_directory'])
    inventory = (phase_dir / 'Inventory.lean').read_bytes()
    source = (phase_dir / own['raw_source']).read_bytes()
    tests = dict(
        queue_manifest_hash=sha(raw_manifest) == record['manifest_sha256'],
        manifest_target=own['target'] == module,
        manifest_revision=own['revision'] == REVISION,
        target_source_matches_frozen_git=source == blob(module),
        target_source_hash=sha(source) == own['source_sha256'] == record['source_sha256'],
        static_closure_exact=own['closure'] == expected,
        static_closure_count=len(expected) == record['closure_modules'],
        all_closure_source_hashes_match_frozen_git=
            own['closure_source_sha256'] == {dep: sha(blob(dep)) for dep in expected},
        original_inventory_source_hash=
            sha(inventory) == manifest['inventory_sha256'] == record['collector_source_sha256'],
    )
    rows.append(dict(phase=record['phase'], target=module, tests=tests,
                     static_pass=all(tests.values()), closure_modules=len(expected),
                     original_collector_runtime_extra_home_check=
                         b'LAMP-CLOSURE-EXACT' in inventory and b'unexpected' in inventory,
                     native_census='NOT_ASSESSED_BY_STATIC_AUDIT'))
payload = dict(revision=REVISION, queue=str(QUEUE.relative_to(EVIDENCE)),
               queue_sha256=sha(queue_raw), scope='static source manifests only',
               phases=len(rows), all_static_checks_pass=all(r['static_pass'] for r in rows),
               rows=rows,
               qualifications=[
                   'Original prepared collectors assert expected canonical homes are present but do not reject extra TCSlib homes. A separately hashed native hardening overlay is required for runtime exact-closure certification.',
                   'Sparse phases without NUPPT.inArg need closure-local control fallbacks or an explicit global-control coverage qualification; Blocks has zero foreign TCSlib homes.',
                   'No pending native phase or request coverage is claimed complete by this artifact.'])
destination = HERE / 'static-source-review.json'
if destination.exists():
    raise RuntimeError('refusing to overwrite an earlier static review')
destination.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps({k:payload[k] for k in ['revision', 'phases', 'all_static_checks_pass']}, indent=2))
