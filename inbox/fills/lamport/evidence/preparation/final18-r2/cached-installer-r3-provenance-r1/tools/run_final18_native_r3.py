"""Serial final18 snapshot/census/seals/controls/scan queue; preserve every attempt.

python3 -I run_final18_native.py --queue PATH --attempt final18-native-r1
Successful old phases are adopted explicitly with --adopt-through PHASE.
A --pause-file sentinel exits cleanly at the next phase boundary.
Only an exit130 bearing the host-cap interruption marker is automatically retried.
No source files under TCSlib are written. No native command has a timeout.
"""
import argparse
from collections import Counter
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write(path, value):
    if path.exists():
        raise RuntimeError('refusing overwrite: ' + str(path))
    path.write_text(json.dumps(value, indent=2) + '\n')


def cap_interrupted(text, code):
    return code == 130 and 'INTERRUPTED: stopping only our Lean child; preserving the log wrapper' in text


def rows(path):
    return [json.loads(x) for x in path.read_text().splitlines() if x.strip()]


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--queue', required=True)
parser.add_argument('--attempt', required=True)
parser.add_argument('--adopt-through', help='Adopt successful old checks through this phase, without recompiling')
parser.add_argument('--pause-file', help='Exit cleanly before a new phase if this sentinel exists')
args = parser.parse_args()
queue_path = Path(args.queue).resolve()
queue = json.loads(queue_path.read_text())
records = queue['records']
root, evidence = Path(records[0]['root']), Path(records[0]['evidence'])
output = evidence / 'logs' / args.attempt
assert not output.exists(), output
output.mkdir()
(output / 'run_final18_native.py').write_bytes(Path(__file__).read_bytes())
(output / 'queue.json').write_bytes(queue_path.read_bytes())
audit_path = evidence / 'inputs/final-r2-order-audit.json'
audit = json.loads(audit_path.read_text())
comparison = json.loads((evidence / 'logs/final-sweep-comparison-r2/report.json').read_text())
assert comparison['status'] == 'PASS' and comparison['expected_modules'] == 177
assert comparison['final_admission_declaration_count'] == 21
gate = queue.get('activation_gate')
if gate:
    qualification_raw = Path(gate['full_planted_qualification_summary']).read_bytes()
    assert sha(qualification_raw) == gate['full_planted_qualification_summary_sha256']
    qualification = json.loads(qualification_raw)
    assert qualification['queue_complete'] and qualification['expected_probes'] == qualification['checked_probes'] == 8
    assert qualification['status_counts'] == {'SOURCE_PASS': 2, 'CONTROL_PASS': 6}
    assert qualification['all_harnesses_and_controls_valid'] and qualification['all_source_seals_pass']
for item in queue['inventory_hardening']['tool_versions'].values():
    assert sha(Path(item['snapshot']).read_bytes()) == item['sha256'], item


def frozen():
    head = subprocess.check_output(['git', '--no-optional-locks', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    assert head == queue['revision'], (head, queue['revision'])
    current = {m: sha((root / (m + '.lean')).read_bytes()) for m in audit['source_sha256']}
    assert current == audit['source_sha256'], 'frozen source hash mismatch'
    return current


def command_log(command, path, quiet=False):
    assert not path.exists(), path
    print('COMMAND ' + ' '.join(command), flush=True)
    with path.open('w') as log:
        log.write('START ' + now() + '\nCOMMAND ' + json.dumps(command) + '\n')
        log.flush()
        if quiet:
            process = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        else:
            process = subprocess.Popen(command, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            for line in process.stdout:
                log.write(line)
                log.flush()
                print(line, end='', flush=True)
            process.wait()
        log.write('END ' + now() + '\nEXIT ' + str(process.returncode) + '\n')
    return process.returncode


def check_module(record, kind, folder, adopt=False):
    module, initial = record[kind + '_module'], record[kind + '_attempt']
    number = 1
    attempts = []
    while True:
        attempt = re.sub(r'01$', f'{number:02}', initial)
        raw = evidence / 'logs/helper-checks' / (module.split('/')[-1] + '-' + attempt + '.log')
        if adopt:
            assert number == 1 and raw.exists()
        else:
            code = command_log(['python3', '-I', queue['check_helper_tool'], module, attempt],
                               folder / (kind + f'-invocation-{number:02}.log'), quiet=True)
        raw_text = raw.read_text()
        found = [x for x in rows(evidence / 'logs/helper-checks/results.jsonl')
                 if x['module'] == module and x['attempt'] == attempt]
        assert len(found) == 1, (module, attempt)
        result = found[0]
        if not adopt:
            assert code == result['exit']
        expected_sha = record['collector_source_sha256'] if kind == 'collector' else record['source_sha256']
        assert result['source_sha256'] == expected_sha
        assert len(re.findall(r'^exit=' + str(result['exit']) + r'$', raw_text, re.M)) == 1
        attempts.append(dict(attempt=attempt, raw_log=str(raw), raw_log_sha256=sha(raw.read_bytes()), result=result))
        if result['exit'] == 0:
            assert not re.search(r'(?m)^.*\.lean:\d+:\d+: error(?:\([^)]*\))?:|^error:', raw_text)
            return raw, attempts
        if not cap_interrupted(raw_text, result['exit']):
            write(folder / (kind + '-failure.json'), attempts)
            raise RuntimeError(kind + ' native failure: ' + str(raw))
        print('HOST_CAP_RETRY ' + str(raw), flush=True)
        number += 1
        adopt = False


def census(record, raw, folder):
    text = raw.read_text()
    target = record['target']
    ends = [x.split('\t') for x in text.splitlines() if x.startswith('LAMP-INVENTORY-END\t')]
    exact = [x.split('\t') for x in text.splitlines() if x.startswith('LAMP-CLOSURE-EXACT\t')]
    assert len(ends) == len(exact) == 1
    assert ends[0][1] == exact[0][1] == target
    assert int(ends[0][4]) == int(exact[0][2]) == record['closure_modules']
    catalog = [x.split('\t') for x in text.splitlines() if x.startswith('LAMP-CATALOG\t')]
    axioms = []
    for line in text.splitlines():
        if line.startswith('LAMP-AXIOMS\t'):
            _, actual_target, constant, value = line.split('\t')
            assert actual_target == target
            assert value.startswith('[') and value.endswith(']')
            names = [] if value == '[]' else value[1:-1].split(', ')
            axioms.append(dict(constant=constant, axioms=names))
    manifest = json.loads(Path(record['manifest']).read_text())
    own = manifest['records'][0]['snapshot_module']
    assert len(catalog) == int(ends[0][2])
    assert len(axioms) == int(ends[0][3])
    assert len({x['constant'] for x in axioms}) == len(axioms)
    assert {x[2] for x in catalog if x[3] == own} == {x['constant'] for x in axioms}
    unexpected = [x for x in axioms if set(x['axioms']) - {'propext', 'Classical.choice', 'Quot.sound'}]
    result = dict(target=target, status='UNEXPECTED_AXIOMS' if unexpected else 'ALL_STORED_CONSTANT_AXIOMS_STANDARD_SUBSET',
                  raw_log=str(raw), raw_log_sha256=sha(raw.read_bytes()), catalog_rows=len(catalog),
                  exact_closure=record['closure_modules'], count=len(axioms), records=axioms, unexpected=unexpected)
    write(folder / 'census.json', result)
    assert not unexpected, unexpected
    return result


def append_generator_provenance(attempt, generator):
    raw = generator.read_bytes()
    copied = attempt / 'actual_prepare_seals.py'
    if copied.exists():
        assert copied.read_bytes() == raw, 'existing actual-generator copy differs'
    else:
        copied.write_bytes(raw)
    incidental = attempt / 'prepare_seals.py'
    manifest = attempt / 'seal-manifest.json'
    record = dict(actual_generator_path=str(generator), actual_generator_sha256=sha(raw),
                  actual_generator_copy='actual_prepare_seals.py',
                  native_attempt_manifest_sha256=sha(manifest.read_bytes()),
                  annotating_driver_path=str(Path(__file__).resolve()),
                  annotating_driver_sha256=sha(Path(__file__).read_bytes()),
                  automatic_copy_present=incidental.exists())
    if incidental.exists():
        copied_sha = sha(incidental.read_bytes())
        record['automatic_copy_sha256'] = copied_sha
        record['automatic_copy_role'] = 'ACTUAL_SOURCE_GENERATOR' if copied_sha == sha(raw) else 'INCIDENTAL_REFERENCE_NOT_SOURCE_GENERATOR'
    provenance = attempt / 'actual-generator-provenance.json'
    if provenance.exists():
        previous = json.loads(provenance.read_text())
        assert previous['actual_generator_sha256'] == record['actual_generator_sha256']
        assert previous['native_attempt_manifest_sha256'] == record['native_attempt_manifest_sha256']
    else:
        write(provenance, record)


def seals(record, folder, adopt=False):
    phase = record['phase']
    phase_dir = Path(record['phase_directory'])
    generator_queue = json.loads(Path(queue['adopted_native_queue']['path']).read_text()) if adopt else queue
    generator = Path(generator_queue['prepare_tool'])
    manifest_path = phase_dir / 'seal-manifest.json'
    manifest = json.loads(manifest_path.read_text())
    assert len(manifest['probes']) == (2 if record['closure_modules'] == 0 else 8)
    pending, selected, attempts = manifest['probes'], {}, []
    number = 1
    while pending:
        name = phase.lower() + '-native-r' + str(number)
        if adopt:
            assert number == 1 and (evidence / 'logs/seals' / name / 'summary.json').exists()
        else:
            current = manifest_path
            if number > 1:
                current = phase_dir / ('seal-manifest-capretry-r' + str(number) + '.json')
                write(current, dict(manifest, probes=pending))
            command_log(['python3', '-I', queue['run_seals_tool'], '--root', str(root), '--evidence', str(evidence),
                         '--manifest', str(current), '--attempt', name], folder / ('seals-invocation-r' + str(number) + '.log'))
        attempt = evidence / 'logs/seals' / name
        append_generator_provenance(attempt, generator)
        actual = rows(attempt / 'results.jsonl')
        assert {x['label'] for x in actual} == {x['label'] for x in pending}, 'incomplete native probe queue'
        attempts.append(str(attempt))
        retry = []
        for result in actual:
            raw = evidence / result['raw_log']
            assert sha(raw.read_bytes()) == result['raw_log_sha256']
            if cap_interrupted(raw.read_text(), result['exit']):
                retry.append(next(x for x in pending if x['label'] == result['label']))
                print('HOST_CAP_RETRY ' + str(raw), flush=True)
            else:
                selected[result['label']] = dict(result, selected_attempt=str(attempt))
        pending = retry
        number += 1
        adopt = False
    assert set(selected) == {x['label'] for x in manifest['probes']}
    write(folder / 'seal-selection.json', dict(attempts=attempts, records=list(selected.values())))
    failures = [x for x in selected.values() if x['status'] not in ('SOURCE_PASS', 'SOURCE_FAIL', 'CONTROL_PASS')]
    afail = [x for x in selected.values() if x.get('mode') == 'A' and x['status'] != 'SOURCE_PASS']
    bfail = [x for x in selected.values() if x.get('mode') == 'B' and x['status'] == 'SOURCE_FAIL']
    return dict(attempts=attempts, counts=dict(Counter(x['status'] for x in selected.values())),
                A_failures=[x['label'] for x in afail], harness_control_process_failures=[x['label'] for x in failures],
                B_failures=[dict(label=x['label'], errors=x['errors'], declarations=sorted({d['declaration'] for d in x['diagnostics']
                            if d['severity'] == 'error' and d.get('declaration')}, key=str)) for x in bfail])


completed = []
phase_names = [r['phase'] for r in records]
assert args.adopt_through is None or args.adopt_through in phase_names
adopt_index = phase_names.index(args.adopt_through) if args.adopt_through else -1
for record in records:
    phase = record['phase']
    if args.pause_file and Path(args.pause_file).exists():
        write(output / 'PAUSED.json', dict(next_phase=phase, completed=len(completed), reason='phase-boundary sentinel', end=now()))
        print('PAUSED_BEFORE ' + phase, flush=True)
        sys.exit(0)
    folder = output / phase
    folder.mkdir()
    print('PHASE_START ' + phase, flush=True)
    before = frozen()
    write(folder / 'source-hashes-before.json', before)
    adopt = phase_names.index(phase) <= adopt_index
    snapshot, snapshot_attempts = check_module(record, 'snapshot', folder, adopt)
    catalog, collector_attempts = check_module(record, 'collector', folder, adopt)
    axs = census(record, catalog, folder)
    if not adopt:
        code = command_log(['python3', '-I', queue['prepare_tool'], 'prepare', '--root', str(root),
                            '--evidence', str(evidence), '--phase', phase, '--catalog-log', str(catalog)],
                            folder / 'prepare.log', quiet=True)
        assert code == 0, 'seal preparation failed'
    seal_result = seals(record, folder, adopt)
    scan_path = Path(record['phase_directory']) / 'explicit-unfold-scan.json'
    if adopt and scan_path.exists():
        write(folder / 'scan-adoption.json', dict(path=str(scan_path), sha256=sha(scan_path.read_bytes()), frozen_source=True))
    else:
        code = command_log(['python3', '-I', queue['prepare_tool'], 'scan', '--root', str(root), '--evidence', str(evidence),
                            '--phase', phase, '--catalog-log', str(catalog), record['target']], folder / 'scan.log', quiet=True)
        assert code == 0, 'explicit unfold scan failed'
    (folder / 'explicit-unfold-scan.json').write_bytes(scan_path.read_bytes())
    after = frozen()
    assert before == after
    write(folder / 'source-hashes-after.json', after)
    summary = dict(phase=phase, target=record['target'], revision=queue['revision'], end=now(),
                   snapshot_attempts=snapshot_attempts, collector_attempts=collector_attempts,
                   stored_own_constants=axs['count'], exact_foreign_closure=axs['exact_closure'],
                   own_axioms=axs['status'], explicit_scan=str(scan_path), seals=seal_result,
                   source_hashes_unchanged=True, native_results_adopted=adopt,
                   adopted_native_queue=queue.get('adopted_native_queue') if adopt else None)
    write(folder / 'summary.json', summary)
    completed.append(summary)
    with (output / 'completed.jsonl').open('a') as log:
        log.write(json.dumps(summary) + '\n')
    print('PHASE_COMPLETE ' + phase + ' ' + json.dumps(seal_result), flush=True)
    if seal_result['A_failures'] or seal_result['harness_control_process_failures']:
        write(output / 'PAUSED.json', dict(phase=phase, reason='A or harness/control/process failure', completed=len(completed)))
        sys.exit(3)
write(output / 'summary.json', dict(status='NATIVE_QUEUE_COMPLETE', revision=queue['revision'], count=len(completed),
                                  phases=completed, end=now()))
print('ALL_PHASES_COMPLETE ' + str(len(completed)), flush=True)
