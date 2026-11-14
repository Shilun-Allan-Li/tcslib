"""Review completed native final18 collectors and generated request sets only.

Run as python3 -I with --output FRESH_BASENAME.json. This tool never starts
Lean/Lake, prepares phases, or changes TCSlib, probes, manifests or raw logs.
Pending collectors/request generation remain explicitly pending.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).parent
EVIDENCE = HERE.parent.parent
ORIGINAL = EVIDENCE / 'preparation/final18-r2/queue.json'
OVERLAY = EVIDENCE / 'preparation/final18-r2/native-hardening-r1/queue.json'
REVISION = '47ced271090f45918645c842cd358c5079092754'
ALLOWED_AXIOMS = {'Classical.choice', 'Quot.sound', 'propext'}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_text())


def catalog(raw, target):
    rows, own_axioms, ends, exact = [], {}, [], []
    for line in raw.decode().splitlines():
        if line.startswith('LAMP-CATALOG\t'):
            fields = line.split('\t')
            if len(fields) != 8 or fields[1] != target:
                raise RuntimeError('malformed or wrong-target catalog row')
            _, _, spelling, home, definition, instance, matcher, status = fields
            rows.append(dict(spelling=spelling, home=home,
                             is_definition=definition == 'true',
                             instance=instance == 'true', matcher=matcher == 'true',
                             status=status.rsplit('.', 1)[-1]))
        elif line.startswith('LAMP-AXIOMS\t'):
            _, name_target, name, values = line.split('\t', 3)
            if name_target != target or name in own_axioms:
                raise RuntimeError('wrong-target or duplicate axiom row')
            own_axioms[name] = [value.strip() for value in values.strip('[]').split(',')
                                if value.strip()]
        elif line.startswith('LAMP-INVENTORY-END\t'):
            fields = line.split('\t')
            if len(fields) != 5 or fields[1] != target:
                raise RuntimeError('malformed inventory end')
            ends.append(tuple(map(int, fields[2:])))
        elif line.startswith('LAMP-CLOSURE-EXACT\t'):
            fields = line.split('\t')
            if len(fields) != 3 or fields[1] != target:
                raise RuntimeError('malformed exact closure marker')
            exact.append(int(fields[2]))
    return rows, own_axioms, ends, exact


def helper_results():
    path = EVIDENCE / 'logs/helper-checks/results.jsonl'
    result = []
    for line in path.read_text().splitlines():
        try:
            result.append(json.loads(line))
        except json.JSONDecodeError:
            # A concurrent append may leave only its final line unfinished.
            continue
    return result


def request_key(row):
    return (row['spelling'], row['home'])


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', required=True)
args = parser.parse_args()
if Path(args.output).name != args.output or not args.output.endswith('.json'):
    raise RuntimeError('output must be a fresh JSON basename in the sole audit directory')
destination = HERE / args.output
if destination.exists():
    raise RuntimeError('refusing to overwrite earlier audit')

original_raw, overlay_raw = ORIGINAL.read_bytes(), OVERLAY.read_bytes()
original, overlay = json.loads(original_raw), json.loads(overlay_raw)
assert original['revision'] == overlay['revision'] == REVISION
assert len(original['records']) == len(overlay['records']) == 18
static_path = HERE / 'static-source-review.json'
static = load(static_path)
assert static['all_static_checks_pass'] and static['revision'] == REVISION
hardening = overlay['inventory_hardening']
original_records = {row['phase']: row for row in original['records']}
frozen_sources = {}
for record in original['records']:
    manifest = load(Path(record['manifest']))
    own = manifest['records'][0]
    frozen_sources[record['target'].replace('.', '/')] = own['source_sha256']
    for module, digest in own['closure_source_sha256'].items():
        key = module.replace('.', '/')
        if key in frozen_sources and frozen_sources[key] != digest:
            raise RuntimeError('inconsistent frozen source hash')
        frozen_sources[key] = digest
overlay_tests = dict(
    original_queue_hash=hardening['original_queue_sha256'] == sha(original_raw),
    original_queue_backup=(OVERLAY.parent / 'queue.original.json').read_bytes() == original_raw,
    all_177_sources_preserved=len(frozen_sources) == 177 and
        hardening['source_sha256_before'] == hardening['source_sha256_after'] == frozen_sources,
    completed_sweep_reference_hash=sha(Path(hardening['completed_final_sweep_comparison']).read_bytes()) ==
        hardening['completed_final_sweep_comparison_sha256'],
    all_versioned_tool_hashes=all(sha(Path(item['snapshot']).read_bytes()) == item['sha256']
        for item in hardening['tool_versions'].values()),
)
checks = helper_results()
phases = []
for record in overlay['records']:
    phase = record['phase']
    initial = original_records[phase]
    directory = Path(record['phase_directory'])
    manifest = load(Path(record['manifest']))
    own = manifest['records'][0]
    hardened_path = Path(record['collector_hardened_source'])
    hardened = hardened_path.read_bytes()
    original_inventory = hardened_path.parent / 'Inventory.original.lean'
    tests = dict(
        original_manifest_unchanged=sha(Path(record['manifest']).read_bytes()) == initial['manifest_sha256'],
        original_manifest_backup=load(hardened_path.parent / 'manifest.original.json') == manifest,
        original_inventory_hash=sha(original_inventory.read_bytes()) ==
            initial['collector_source_sha256'] == record['collector_original_source_sha256'],
        native_inventory_hash=sha(hardened) == record['collector_source_sha256'],
        exact_guard_present=all(token in hardened for token in [
            b'for imported in env.header.moduleNames',
            b'if (`TCSlib).isPrefixOf imported then',
            b'unless homes.contains imported.toString do',
            b'unless exactHomes == homes.length do', b'LAMP-CLOSURE-EXACT']),
        unchanged_target_and_closure=all(record[key] == initial[key]
            for key in ['target', 'revision', 'closure_modules', 'source_sha256', 'snapshot_module']),
    )
    item = dict(phase=phase, target=record['target'], overlay_tests=tests,
                overlay_pass=all(tests.values()), native_census='PENDING', request_coverage='PENDING')
    module = record['collector_module'].replace('.', '/')
    passes = [row for row in checks if row['module'] == module and row['exit'] == 0 and
              row['source_sha256'] == record['collector_source_sha256']]
    if not passes:
        phases.append(item)
        continue
    check = passes[-1]
    log_path = EVIDENCE / check['log']
    log_raw = log_path.read_bytes()
    log_text = log_raw.decode()
    rows, axioms, ends, exact = catalog(log_raw, record['target'])
    own_rows = [row for row in rows if row['home'] == own['snapshot_module']]
    names = [request_key(row) for row in rows]
    own_names = {row['spelling'] for row in own_rows}
    bad_axioms = {name: sorted(set(values) - ALLOWED_AXIOMS) for name, values in axioms.items()
                  if set(values) - ALLOWED_AXIOMS}
    census_tests = dict(
        raw_check_completed=log_text.rstrip().endswith('exit=0'),
        native_source_bound=('source-sha256=' + record['collector_source_sha256']) in log_text,
        no_lean_error_diagnostic=re.search(r'\.lean:\d+:\d+: error:', log_text) is None,
        exact_runtime_closure=exact == [len(own['closure'])],
        complete_catalog_counts=ends == [(len(rows), len(axioms), len(own['closure']))],
        catalog_name_home_unique=len(names) == len(set(names)),
        every_own_stored_constant_has_axiom_row=own_names == set(axioms),
        no_catalog_home_outside_declared_environment=all(
            row['home'] == own['snapshot_module'] or row['home'] in own['closure'] for row in rows),
        standard_axioms_only=not bad_axioms,
    )
    imported = [row for row in rows if row['home'] != own['snapshot_module']]
    eligible = [row for row in imported if row['is_definition'] and not row['instance']
                and row['status'] != 'reducible']
    item.update(native_census='PASS' if all(census_tests.values()) else 'ISSUE',
                census_tests=census_tests, collector_log=check['log'], collector_log_sha256=sha(log_raw),
                catalog_rows=len(rows), own_stored_constants=len(own_rows),
                own_axiom_set_counts=dict(Counter(','.join(values) for values in axioms.values())),
                nonstandard_axioms=bad_axioms,
                imported_constants=len(imported), imported_eligible_definitions=len(eligible),
                imported_instance_definitions=sum(row['is_definition'] and row['instance'] for row in imported),
                imported_reducible_noninstance_definitions=sum(row['is_definition'] and
                    not row['instance'] and row['status'] == 'reducible' for row in imported),
                eligible_matchers=sum(row['matcher'] for row in eligible),
                eligible_private_names=sum(row['spelling'].startswith('_private.') for row in eligible))
    seal_path = directory / 'seal-manifest.json'
    if not seal_path.exists():
        phases.append(item)
        continue
    try:
        seal_manifest = load(seal_path)
    except json.JSONDecodeError:
        item['request_coverage'] = 'PENDING_MANIFEST_WRITE'
        phases.append(item)
        continue
    source_probes = [probe for probe in seal_manifest['probes'] if not probe.get('control')]
    request_tests = dict(bound_to_native_catalog=seal_manifest['inventory_log_sha256'] == sha(log_raw),
                         exactly_A_and_B=sorted(probe.get('mode') for probe in source_probes) == ['A', 'B'])
    mode_reviews = []
    for probe in source_probes:
        mode = probe['mode']
        expected = [row for row in eligible if mode == 'B' or row['spelling'] != 'Complexity.PolyExpr.eval']
        expected_keys, actual_keys = set(map(request_key, expected)), set(map(request_key, probe['requests']))
        source_path = directory / 'probes' / (probe['label'] + '.lean')
        request_path = directory / 'requests' / (probe['label'] + '.json')
        mode_tests = dict(request_set_complete=expected_keys == actual_keys,
                          request_rows_exact=sorted(expected, key=request_key) ==
                              sorted(probe['requests'], key=request_key),
                          request_rows_unique=len(probe['requests']) == len(actual_keys),
                          target_and_source_bound=probe['target'] == record['target'] and
                              probe['source_sha256'] == record['source_sha256'],
                          probe_source_hash=source_path.is_file() and
                              sha(source_path.read_bytes()) == probe['probe_sha256'],
                          request_record_preserved=request_path.is_file() and load(request_path) == probe)
        mode_reviews.append(dict(mode=mode, tests=mode_tests, expected_requests=len(expected),
                                 actual_requests=len(probe['requests']),
                                 missing=sorted(expected_keys - actual_keys), unexpected=sorted(actual_keys - expected_keys)))
    item.update(request_coverage='PASS' if all(request_tests.values()) and
                    all(all(row['tests'].values()) for row in mode_reviews) else 'ISSUE',
                request_tests=request_tests, mode_reviews=mode_reviews,
                source_request_manifest=str(seal_path.relative_to(EVIDENCE)),
                source_request_manifest_sha256=sha(seal_path.read_bytes()),
                generated_controls=sum(bool(probe.get('control')) for probe in seal_manifest['probes']))
    phases.append(item)

issues = [row['phase'] for row in phases if not row['overlay_pass'] or row['native_census'] == 'ISSUE'
          or row['request_coverage'] == 'ISSUE']
payload = dict(revision=REVISION, original_queue_sha256=sha(original_raw), native_queue_sha256=sha(overlay_raw),
               static_source_review_sha256=sha(static_path.read_bytes()),
               overlay_tests=overlay_tests, overlay_pass=all(overlay_tests.values()),
               native_censuses_completed=sum(row['native_census'] == 'PASS' for row in phases),
               request_sets_completed=sum(row['request_coverage'] == 'PASS' for row in phases),
               phases_requested=len(phases), issue_phases=issues, phases=phases,
               scope='Independent census, own-axiom and generated request eligibility/coverage audit. Seal source failures and control result interpretation are separately reviewed by route_audit. Pending phases are not claimed complete.')
destination.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps({key:payload[key] for key in ['overlay_pass', 'native_censuses_completed',
      'request_sets_completed', 'phases_requested', 'issue_phases']}, indent=2))
for row in phases:
    if row['native_census'] != 'PENDING':
        print(row['phase'], row['native_census'], row.get('own_stored_constants'),
              'own constants;', row['request_coverage'], 'requests')
