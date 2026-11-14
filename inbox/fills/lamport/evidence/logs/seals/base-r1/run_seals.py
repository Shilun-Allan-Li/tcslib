"""Run prepared seals serially and retain every source, tool, diagnostic and raw log.

Usage: python3 -I run_seals.py --root PROOF --evidence EVIDENCE
         --manifest EVIDENCE/seals/PHASE/seal-manifest.json --attempt NAME

There is no timeout and no concurrency. Whole-file source errors and expected control
errors never stop the queue. A resource failure stops it for the coordinator's E-RES
handling. The final exit code is nonzero for any failed whole-file seal, harness, process
or control, even though the entire non-resource queue has been checked.
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


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def json_write(path, data):
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')


def no_comments(text):
    chars, depth, index = list(text), 0, 0
    while index < len(text):
        if text.startswith('/-', index):
            depth += 1
            size = 2
        elif depth and text.startswith('-/', index):
            depth -= 1
            size = 2
        elif depth:
            size = 1
        elif text.startswith('--', index):
            end = text.find('\n', index)
            size = (len(text) if end == -1 else end) - index
        else:
            index += 1
            continue
        for k in range(index, index + size):
            if chars[k] != '\n':
                chars[k] = ' '
        index += size
    return ''.join(chars)


def original_maps(raw, probe, given):
    if given:
        return given
    # Compatibility with probes prepared before original_line_map was added.
    lines = raw.decode().splitlines(keepends=True)
    code = no_comments(raw.decode()).splitlines()
    imports = [i for i, line in enumerate(code) if line.strip().startswith('import ')]
    if not imports:
        raise RuntimeError('cannot recover legacy source map without imports')
    split = imports[-1] + 1
    header, body = ''.join(lines[:split]), ''.join(lines[split:])
    text = probe.decode()
    if text.count(header) != 1 or text.count(body) != 1:
        raise RuntimeError('legacy original source does not occur uniquely in probe')
    hstart, bstart = text.index(header), text.index(body)
    if hstart >= bstart:
        raise RuntimeError('legacy original source pieces appear out of order')
    hline = text.count('\n', 0, hstart) + 1
    bline = text.count('\n', 0, bstart) + 1
    return [dict(original_start=1, original_end=split, generated_start=hline,
                 generated_end=hline + split - 1),
            dict(original_start=split + 1, original_end=len(lines), generated_start=bline,
                 generated_end=bline + len(lines) - split - 1)]


def declarations(raw):
    stack, result = [], []
    namespace = ''
    decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b\s*([^\s(:{]*)")
    for index, line in enumerate(no_comments(raw.decode()).splitlines(), 1):
        line = line.strip()
        start = re.match(r'^(namespace|section)(?:\s+(\S+))?\s*$', line)
        if start:
            kind, name = start.groups()
            stack.append((kind, name, namespace))
            if kind == 'namespace':
                namespace = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None, (namespace, name)))
            continue
        if re.match(r'^end(?:\s+\S+)?\s*$', line):
            if stack:
                _, _, namespace = stack.pop()
            continue
        match = decl.match(line)
        if match:
            kind, name = match.groups()
            name = name or f'<anonymous {kind} at line {index}>'
            full = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None, (namespace, name)))
            result.append(dict(line=index, kind=kind, name=full))
    return result


def diagnostics(text, source_maps, decls, probe_path, target):
    located = re.compile(r'^(.*?\.lean):(\d+):(\d+): (error|warning)(?:\(([^)]+)\))?:\s*(.*)$')
    global_error = re.compile(r'^error(?:\(([^)]+)\))?:\s*(.*)$')
    starts, output = [], []
    lines = text.splitlines()
    for i, line in enumerate(lines):
        match = located.match(line)
        if match:
            file, lineno, column, severity, code, message = match.groups()
            item = dict(file=file, line=int(lineno), column=int(column), severity=severity,
                        code=code, message=message, raw_log_line=i + 1)
        else:
            match = global_error.match(line)
            if not match:
                continue
            code, message = match.groups()
            item = dict(file=None, line=None, column=None, severity='error', code=code,
                        message=message, raw_log_line=i + 1)
        starts.append((i, item))
    for number, (start, item) in enumerate(starts):
        end = starts[number + 1][0] if number + 1 < len(starts) else len(lines)
        item['raw_diagnostic_block'] = '\n'.join(lines[start:end])
        item['original_file'] = None
        item['original_line'] = None
        item['declaration'] = None
        if item['file'] and item['file'].replace('\\', '/').endswith(probe_path + '.lean'):
            for mapping in source_maps:
                if mapping['generated_start'] <= item['line'] <= mapping['generated_end']:
                    original = mapping['original_start'] + item['line'] - mapping['generated_start']
                    item['original_file'] = target.replace('.', '/') + '.lean'
                    item['original_line'] = original
                    preceding = [d for d in decls if d['line'] <= original]
                    if preceding:
                        item['declaration'] = preceding[-1]['name']
                    break
        output.append(item)
    return output


def harness(text, record):
    if record.get('control') and record.get('expected_errors') == 0 and not record['requests']:
        return dict(valid=True, unsealed=True, issues=[])
    label, requests = record['label'], record['requests']
    issues, expected = [], [(r['spelling'], r['home']) for r in requests]
    if len(set(expected)) != len(expected):
        issues.append('duplicate request')
    for operation in ('INSTALL', 'EOF'):
        wanted = f'LAMP-SEAL-{operation}\t{label}\t{len(requests)}'
        summaries = [line for line in text.splitlines() if line.startswith(f'LAMP-SEAL-{operation}\t{label}\t')]
        if summaries != [wanted]:
            issues.append(f'{operation} completion marker missing/duplicated/count differs')
        prefix = f'LAMP-SEAL-NAME\t{label}\t{operation}\t'
        seen = []
        for line in text.splitlines():
            if line.startswith(prefix):
                fields = line[len(prefix):].split('\t')
                if len(fields) != 2:
                    issues.append(f'{operation} malformed name row')
                else:
                    seen.append(tuple(fields))
        if Counter(seen) != Counter(expected):
            issues.append(f'{operation} per-name coverage differs')
    if re.search(r'(?m)^.*error(?:\([^)]*\))?:.*LAMP-HARNESS', text):
        issues.append('explicit harness diagnostic')
    return dict(valid=not issues, unsealed=False, requested=len(requests), issues=issues)


def run(args):
    root, evidence, manifest_path = Path(args.root).resolve(), Path(args.evidence).resolve(), Path(args.manifest).resolve()
    manifest_raw = manifest_path.read_bytes()
    manifest = json.loads(manifest_raw)
    preparation_raw = (manifest_path.parent / 'manifest.json').read_bytes()
    preparation = json.loads(preparation_raw)
    originals = {r['target']: r for r in preparation['records'] if not r.get('absent_at_revision')}
    attempt = evidence / 'logs' / 'seals' / args.attempt
    if attempt.exists():
        raise RuntimeError(f'refusing to overwrite attempt {attempt}')
    attempt.mkdir(parents=True)
    (attempt / 'sources').mkdir()
    (attempt / 'seal-manifest.json').write_bytes(manifest_raw)
    (attempt / 'preparation-manifest.json').write_bytes(preparation_raw)
    (attempt / 'run_seals.py').write_bytes(Path(__file__).read_bytes())
    (attempt / 'lean_check_tree.sh').write_bytes((root / 'scripts/lean_check_tree.sh').read_bytes())
    prep_tool = Path(__file__).with_name('prepare_seals.py')
    if prep_tool.exists():
        (attempt / 'prepare_seals.py').write_bytes(prep_tool.read_bytes())
    head = subprocess.run(['git', '--no-optional-locks', '-C', str(root), 'rev-parse', 'HEAD'],
                          capture_output=True, text=True).stdout.strip()
    json_write(attempt / 'metadata.json', dict(root=str(root), evidence=str(evidence),
        manifest=str(manifest_path), manifest_sha256=digest(manifest_raw), start=utc_now(),
        head=head, platform=sys.platform, serial=True, timeout=None,
        maximum_resident_set_size_units='bytes (Darwin /usr/bin/time -l)',
        script_sha256=digest(Path(__file__).read_bytes())))
    results, resource_stop = [], False
    for record in manifest['probes']:
        module = record['module']
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*', module):
            raise RuntimeError('invalid module name: ' + module)
        probe_path = module.replace('.', '/')
        source_raw = (root / (probe_path + '.lean')).read_bytes()
        if digest(source_raw) != record['probe_sha256']:
            raise RuntimeError('probe SHA differs: ' + module)
        (attempt / 'sources' / (record['label'] + '.lean')).write_bytes(source_raw)
        original_raw, maps, decls = None, [], []
        if record.get('target'):
            original = originals[record['target']]
            original_raw = (manifest_path.parent / original['raw_source']).read_bytes()
            if digest(original_raw) != record['source_sha256']:
                raise RuntimeError('original source SHA differs: ' + module)
            (attempt / 'sources' / (record['label'] + '.original.lean')).write_bytes(original_raw)
            maps = original_maps(original_raw, source_raw, record.get('original_line_map'))
            decls = declarations(original_raw)
        command = ['/usr/bin/time', '-l', 'bash', 'scripts/lean_check_tree.sh', probe_path]
        log_path = attempt / (record['label'] + '.log')
        start = utc_now()
        print(f'START {record["label"]}', flush=True)
        with log_path.open('w') as log:
            log.write(f'START {start}\nSOURCE-SHA256 {digest(source_raw)}\nCOMMAND {command!r}\n')
            log.flush()
            process = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
            end = utc_now()
            log.write(f'END {end}\nEXIT {process.returncode}\n')
        text = log_path.read_text()
        diags = diagnostics(text, maps, decls, probe_path, record.get('target', ''))
        errors = [d for d in diags if d['severity'] == 'error']
        hcheck = harness(text, record)
        resource_stop = bool(re.search(r'No space left on device|os error 28|lean exited with status (?:135|137|139)|error: failed to locate application', text))
        if resource_stop:
            status = 'RESOURCE_STOP'
        elif not hcheck['valid']:
            status = 'HARNESS_FAIL'
        elif record.get('control'):
            expected = record['expected_errors']
            if expected == 0:
                passed = not errors and process.returncode == 0
            else:
                passed = (len(errors) == 1 and errors[0]['line'] == record['expected_error_line']
                          and bool(errors[0]['file']) and errors[0]['file'].endswith(probe_path + '.lean')
                          and process.returncode == 1)
            status = 'CONTROL_PASS' if passed else 'CONTROL_FAIL'
        elif errors and any(e['original_line'] is None for e in errors):
            status = 'HARNESS_FAIL'
            hcheck['issues'].append('error outside original-source line ranges')
            hcheck['valid'] = False
        elif errors:
            status = 'SOURCE_FAIL'
        elif process.returncode:
            status = 'PROCESS_FAIL'
        else:
            status = 'SOURCE_PASS'
        maximum = re.search(r'(?m)^\s*(\d+)\s+maximum resident set size\s*$', text)
        result = dict(label=record['label'], module=module, target=record.get('target'),
            mode=record.get('mode'), start=start, end=end, exit=process.returncode, status=status,
            errors=len(errors), warnings=sum(d['severity'] == 'warning' for d in diags),
            harness=hcheck, diagnostics=diags, original_line_map=maps,
            source_sha256=digest(source_raw), raw_log=str(log_path.relative_to(evidence)),
            raw_log_sha256=digest(log_path.read_bytes()),
            maximum_resident_set_size_bytes=int(maximum[1]) if maximum else None)
        if record.get('control'):
            result.update(expected_errors=record['expected_errors'], expected_error_line=record['expected_error_line'])
        results.append(result)
        json_write(attempt / (record['label'] + '.result.json'), result)
        with (attempt / 'results.jsonl').open('a') as out:
            out.write(json.dumps(result, ensure_ascii=False) + '\n')
        print(f'END {record["label"]}: {status}; {len(errors)} error(s)', flush=True)
        if resource_stop:
            break
    counts = Counter(r['status'] for r in results)
    summary = dict(end=utc_now(), expected_probes=len(manifest['probes']), checked_probes=len(results),
        queue_complete=len(results) == len(manifest['probes']), resource_stop=resource_stop,
        status_counts=dict(counts),
        failing_declarations=sorted({(d['original_file'], d['declaration']) for r in results
            for d in r['diagnostics'] if d['severity'] == 'error' and d['original_line'] is not None},key=str),
        all_harnesses_and_controls_valid=all(r['status'] in ('SOURCE_PASS', 'SOURCE_FAIL', 'CONTROL_PASS') for r in results),
        all_source_seals_pass=not counts.get('SOURCE_FAIL'),
        raw_results='results.jsonl')
    json_write(attempt / 'summary.json', summary)
    print(json.dumps(summary, ensure_ascii=False), flush=True)
    return 0 if summary['queue_complete'] and all(r['status'] in ('SOURCE_PASS','CONTROL_PASS') for r in results) else 1


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--evidence', required=True)
parser.add_argument('--manifest', required=True)
parser.add_argument('--attempt', required=True)
args = parser.parse_args()
if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*', args.attempt):
    raise RuntimeError('attempt must be a simple fresh directory name')
sys.exit(run(args))
