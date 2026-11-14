"""Read-only independent Rule-10 log audit; never invokes Lean or edits probes.

Run as python3 -I with --queue, --output FRESH_DIRECTORY. Pending phases and
interrupted attempts remain explicit. This audits the serialized probe coverage,
source identity, controls and reported source failures. Census/request selection
and manual explicit-unfold classification are independent companion reviews.
"""
import argparse
from collections import Counter
import datetime
import hashlib
import json
from pathlib import Path
import re


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_text())


def fail_if(condition, message, issues):
    if condition:
        issues.append(message)


def markers(text, record):
    if record.get('control') and not record['requests']:
        return []
    label = record['label']
    wanted = Counter((r['spelling'], r['home']) for r in record['requests'])
    issues = []
    fail_if(len(wanted) != len(record['requests']), 'duplicate serialized request', issues)
    lines = text.splitlines()
    for operation in ('INSTALL', 'EOF'):
        prefix = f'LAMP-SEAL-NAME\t{label}\t{operation}\t'
        actual = Counter(tuple(line[len(prefix):].split('\t'))
                         for line in lines if line.startswith(prefix))
        fail_if(actual != wanted, operation + ' per-name multiset differs', issues)
        summaries = [line for line in lines if line.startswith(f'LAMP-SEAL-{operation}\t{label}\t')]
        fail_if(summaries != [f'LAMP-SEAL-{operation}\t{label}\t{len(record["requests"])}'],
                operation + ' summary count/completion differs', issues)
    return issues


def original_source_preserved(source, original, line_map):
    a, b = original.splitlines(keepends=True), source.splitlines(keepends=True)
    seen = []
    for m in line_map:
        x = a[m['original_start'] - 1:m['original_end']]
        y = b[m['generated_start'] - 1:m['generated_end']]
        if x != y:
            return False
        seen.extend(range(m['original_start'], m['original_end'] + 1))
    return seen == list(range(1, len(a) + 1))


def audit_attempt(directory, phase, preparation, manifest, evidence):
    metadata = load(directory / 'metadata.json')
    issues = []
    raw_manifest = (directory / 'seal-manifest.json').read_bytes()
    fail_if(sha(raw_manifest) != sha((phase / 'seal-manifest.json').read_bytes()),
            'attempt manifest differs from phase manifest', issues)
    fail_if(metadata['manifest_sha256'] != sha(raw_manifest), 'manifest SHA differs', issues)
    target_record = preparation['records'][0]
    original = (phase / target_record['raw_source']).read_bytes()
    fail_if(sha(original) != target_record['source_sha256'], 'original SHA differs', issues)
    expected = {r['label']: r for r in manifest['probes']}
    result_file = directory / 'results.jsonl'
    raw_results = result_file.read_text() if result_file.exists() else ''
    # A concurrently running writer may not yet have finished its final row.
    result_lines = raw_results.splitlines()
    if raw_results and not raw_results.endswith('\n'):
        result_lines.pop()
    results = [json.loads(line) for line in result_lines]
    labels = [r['label'] for r in results]
    fail_if(len(labels) != len(set(labels)), 'duplicate result labels', issues)
    fail_if(any(label not in expected for label in labels), 'unexpected result label', issues)
    probes = []
    for result in results:
        record = expected[result['label']]
        probe_issues = []
        source = (directory / 'sources' / (result['label'] + '.lean')).read_bytes()
        fail_if(sha(source) != record['probe_sha256'] or sha(source) != result['source_sha256'],
                'probe SHA differs', probe_issues)
        if record.get('target'):
            fail_if(not original_source_preserved(source.decode(), original.decode(),
                                                  record['original_line_map']),
                    'original source not fully preserved by line map', probe_issues)
        log = evidence / result['raw_log']
        raw = log.read_bytes()
        fail_if(sha(raw) != result['raw_log_sha256'], 'raw log SHA differs', probe_issues)
        text = raw.decode()
        interrupted = result['exit'] == 130
        if not interrupted:
            probe_issues += markers(text, record)
        errors = [d for d in result['diagnostics'] if d['severity'] == 'error']
        fail_if(len(errors) != result['errors'], 'diagnostic count differs', probe_issues)
        if record.get('control') and not interrupted:
            n = record['expected_errors']
            passed = len(errors) == n and result['exit'] == (1 if n else 0)
            if n:
                passed = passed and n == 1 and errors[0]['line'] == record['expected_error_line']
                passed = passed and bool(errors[0]['file']) and errors[0]['file'].endswith(
                    record['module'].replace('.', '/') + '.lean')
            fail_if(not passed, 'paired control did not meet exact error/exit condition', probe_issues)
        failures = [dict(declaration=d['declaration'], original_line=d['original_line'],
                         message=d['message'], raw_log_line=d['raw_log_line']) for d in errors]
        probes.append(dict(label=result['label'], mode=record.get('mode'),
                           control=bool(record.get('control')), status=result['status'],
                           exit=result['exit'], errors=len(errors), interrupted=interrupted,
                           request_count=len(record['requests']), audit_issues=probe_issues,
                           failing_declarations=sorted({d['declaration'] for d in errors
                                                        if d['declaration'] is not None}),
                           failure_locations=failures, raw_log=result['raw_log']))
        issues += [result['label'] + ': ' + item for item in probe_issues]
    terminal = (directory / 'summary.json').exists()
    complete = terminal and labels == [r['label'] for r in manifest['probes']]
    interrupted = any(p['interrupted'] for p in probes)
    statuses_valid = all(p['status'] in ('SOURCE_PASS', 'SOURCE_FAIL', 'CONTROL_PASS') for p in probes)
    accepted = complete and not interrupted and not issues and statuses_valid
    return dict(attempt=directory.name, terminal=terminal, queue_complete=complete,
                interrupted=interrupted, accepted_evidence=accepted, audit_issues=issues,
                probes=probes, metadata_sha256=sha((directory / 'metadata.json').read_bytes()))


def main(args):
    queue_path, output = Path(args.queue).resolve(), Path(args.output).resolve()
    if output.exists():
        raise RuntimeError('refusing to replace audit output')
    queue = load(queue_path)
    evidence = Path(queue['records'][0]['evidence'])
    output.mkdir(parents=True)
    (output / 'tool.py').write_bytes(Path(__file__).read_bytes())
    (output / 'queue.json').write_bytes(queue_path.read_bytes())
    phases = []
    directories = [p for p in (evidence / 'logs' / 'seals').iterdir()
                   if p.is_dir() and (p / 'metadata.json').exists()]
    for entry in queue['records']:
        phase = Path(entry['phase_directory'])
        prep = load(phase / 'manifest.json')
        if not (phase / 'seal-manifest.json').exists():
            phases.append(dict(phase=entry['phase'], target=entry['target'], pending='no seal manifest'))
            continue
        manifest = load(phase / 'seal-manifest.json')
        attempts = []
        for directory in directories:
            meta = load(directory / 'metadata.json')
            if Path(meta['manifest']).resolve() == phase / 'seal-manifest.json':
                attempts.append(audit_attempt(directory, phase, prep, manifest, evidence))
        accepted = [a for a in attempts if a['accepted_evidence']]
        phases.append(dict(phase=entry['phase'], target=entry['target'], attempts=attempts,
                           accepted_attempt=accepted[-1]['attempt'] if accepted else None,
                           expected_probes=len(manifest['probes']),
                           expected_controls=sum(bool(p.get('control')) for p in manifest['probes'])))
    accepted_phases = [p for p in phases if p.get('accepted_attempt')]
    source_a_failures, source_b_failures = [], []
    for phase in accepted_phases:
        attempt = next(a for a in phase['attempts'] if a['attempt'] == phase['accepted_attempt'])
        for probe in attempt['probes']:
            if probe['status'] == 'SOURCE_FAIL':
                (source_a_failures if probe['mode'] == 'A' else source_b_failures).append(
                    dict(phase=phase['phase'], target=phase['target'], **probe))
    result = dict(commit=queue['revision'], created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  source_only=True, queue_sha256=sha(queue_path.read_bytes()),
                  expected_phases=queue['count'], accepted_phases=len(accepted_phases), phases=phases,
                  all_phases_complete=len(accepted_phases) == queue['count'],
                  source_A_failures=source_a_failures, source_B_failures=source_b_failures,
                  qualification='Completion of this log audit does not replace census/selection or explicit-unfold manual review.')
    (output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['commit', 'expected_phases', 'accepted_phases',
                                            'all_phases_complete']}, indent=2))
    print('A source failure phases:', len(source_a_failures), '; B source failure phases:', len(source_b_failures))


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--queue', required=True)
parser.add_argument('--output', required=True)
if __name__ == '__main__':
    main(parser.parse_args())
