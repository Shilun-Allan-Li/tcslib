"""Compare a completed final sweep and its admission set with the issued baseline.

This tool never invokes Lean, Lake, Git mutations, or modifies raw attempts. Run it only
after final sources are stable and prepare_sweep_order.py has pinned their hashes.
Repeated module results are reported as duplicates; no latest-attempt selection is made.
The output directory must be fresh. All comparison inputs and this tool are snapshotted.
"""
import argparse
import ast
from collections import Counter
import datetime
import hashlib
import json
from pathlib import Path
import re
import sys


TARGET = ('TCSlib/Cryptography/Authentication/Signatures/Lamport', 'lamport_oneTimeSecure')
DIAGNOSTIC = re.compile(r'^(.*?\.lean):(\d+):(\d+): (error|warning)(?:\(([^)]+)\))?:\s*(.*)$')
GLOBAL_ERROR = re.compile(r'^error(?:\(([^)]+)\))?:\s*(.*)$')
SORRY = re.compile(r'''declaration uses\s+['"‘`]?sorry['"’`]?''')
DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|opaque|axiom)\b\s*([^\s(:{]*)", re.M)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blank_comments(text):
    chars, index, depth = list(text), 0, 0
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


def source_declarations(raw):
    code = blank_comments(raw.decode())
    return [(code.count('\n', 0, m.start()) + 1, m.group(1))
            for m in DECLARATION.finditer(code)]


def normalize_module(module):
    if module.startswith('TCSlib/'):
        return module
    if module.startswith('Complexity/'):
        return 'TCSlib/' + module
    return 'TCSlib/Complexity/' + module


def issued_admissions(path):
    entries, counts, declared_total = [], [], None
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        if line.startswith('TOTAL '):
            declared_total = int(line.split()[1])
            continue
        module, number, names = line.split(': ', 2)
        names = names.split(', ')
        counts.append(dict(module=normalize_module(module), declared=int(number), actual=len(names)))
        entries.extend((normalize_module(module), name) for name in names)
    return entries, counts, declared_total


def resolve_input(evidence, spelling):
    path = Path(spelling)
    return path.resolve() if path.is_absolute() else (evidence / path).resolve()


def serialize_keys(values):
    return [dict(module=module, declaration=decl) for module, decl in sorted(values)]


def main(args):
    root, evidence = Path(args.root).resolve(), Path(args.evidence).resolve()
    order_path = resolve_input(evidence, args.order)
    audit_path = resolve_input(evidence, args.order_audit)
    results_path = resolve_input(evidence, args.results)
    baseline_path = resolve_input(evidence, args.baseline)
    issued_path = resolve_input(evidence, args.issued)
    output = resolve_input(evidence, args.output)
    if not output.is_relative_to(evidence):
        raise RuntimeError('comparison output must stay inside evidence')
    if output.exists():
        raise RuntimeError('refusing to overwrite comparison attempt: ' + str(output))
    output.mkdir(parents=True)
    inputs = dict(order=order_path, order_audit=audit_path, results=results_path,
                  baseline=baseline_path, issued=issued_path)
    for label, path in inputs.items():
        (output / (label + path.suffix)).write_bytes(path.read_bytes())
    (output / 'compare_final_sweep.py').write_bytes(Path(__file__).read_bytes())
    issues = {name: [] for name in (
        'baseline', 'order', 'malformed_results', 'omitted_modules', 'unexpected_modules',
        'duplicate_module_attempts', 'result_order', 'source_hashes', 'missing_logs',
        'log_protocol', 'nonzero_results', 'error_diagnostics', 'unmapped_sorry_warnings',
        'cross_module_diagnostics', 'duplicate_sorry_warnings', 'admission_difference')}
    expected = [x for x in order_path.read_text().splitlines() if x.strip()]
    duplicate_order = [m for m, count in Counter(expected).items() if count != 1]
    if duplicate_order:
        issues['order'].append(dict(duplicate_modules=duplicate_order))
    audit = json.loads(audit_path.read_text())
    source_hashes = audit.get('source_sha256', {})
    if set(source_hashes) != set(expected):
        issues['order'].append(dict(audit_source_set_differs=True))
    if audit.get('total') != len(expected) or audit.get('exact_issued_subsequence') is not True:
        issues['order'].append(dict(order_audit_metadata_differs=True))
    issued_order = (evidence / 'inputs/order.txt').read_text().splitlines()
    if [m for m in expected if m in set(issued_order)] != issued_order:
        issues['order'].append(dict(issued_150_module_subsequence_differs=True))

    baseline = json.loads(baseline_path.read_text())
    baseline_keys = [(row['module'], row['declaration']) for row in baseline]
    issued_keys, issued_counts, total = issued_admissions(issued_path)
    if len(baseline_keys) != 22 or len(set(baseline_keys)) != 22:
        issues['baseline'].append(dict(baseline_count=len(baseline_keys), expected=22))
    if len(issued_keys) != 22 or len(set(issued_keys)) != 22 or total != 22:
        issues['baseline'].append(dict(issued_count=len(issued_keys), issued_total=total, expected=22))
    if any(row['declared'] != row['actual'] for row in issued_counts):
        issues['baseline'].append(dict(issued_module_counts_differ=issued_counts))
    if set(baseline_keys) != set(issued_keys):
        issues['baseline'].append(dict(issued_and_baseline_declarations_differ=True))
    if baseline_keys.count(TARGET) != 1:
        issues['baseline'].append(dict(target_missing_or_duplicated=True))
    wanted = set(baseline_keys) - {TARGET}

    # Never map a warning through a current source whose bytes do not match the
    # separately prepared final-order audit. A temporary issue-base main therefore
    # cannot be silently treated as the final source.
    declarations, fingerprints = {}, {}
    for module in expected:
        source = root / (module + '.lean')
        if not source.exists():
            issues['source_hashes'].append(dict(module=module, missing=True))
            continue
        raw = source.read_bytes()
        fingerprints[module] = sha(raw)
        if fingerprints[module] != source_hashes.get(module):
            issues['source_hashes'].append(dict(module=module, expected=source_hashes.get(module),
                                                actual=fingerprints[module]))
            continue
        declarations[module] = source_declarations(raw)

    rows = []
    for line_number, line in enumerate(results_path.read_text().splitlines(), 1):
        if not line.strip():
            continue
        try:
            row = json.loads(line)
            if not isinstance(row, dict) or not isinstance(row.get('module'), str):
                raise ValueError('missing module')
            if type(row.get('exit')) is not int or not isinstance(row.get('log'), str):
                raise ValueError('missing integer exit or raw-log path')
        except (ValueError, json.JSONDecodeError) as error:
            issues['malformed_results'].append(dict(line=line_number, error=str(error), raw=line))
            continue
        row['_results_line'] = line_number
        rows.append(row)
    by_module = {}
    for row in rows:
        by_module.setdefault(row['module'], []).append(row)
    issues['omitted_modules'] = [m for m in expected if m not in by_module]
    issues['unexpected_modules'] = sorted(set(by_module) - set(expected))
    issues['duplicate_module_attempts'] = [dict(module=m, results_lines=[r['_results_line'] for r in values])
        for m, values in sorted(by_module.items()) if len(values) > 1]
    if [row['module'] for row in rows] != expected:
        issues['result_order'].append(dict(actual=[row['module'] for row in rows], expected=expected))

    admissions, all_diagnostics, log_fingerprints, module_results = [], [], {}, []
    for row in rows:
        module, line_number = row['module'], row['_results_line']
        if row.get('source_sha256') and row['source_sha256'] != source_hashes.get(module):
            issues['source_hashes'].append(dict(module=module, results_line=line_number,
                result_source_sha256=row['source_sha256'], expected=source_hashes.get(module)))
        if row.get('source_after_sha256') and row['source_after_sha256'] != source_hashes.get(module):
            issues['source_hashes'].append(dict(module=module, results_line=line_number,
                result_source_after_sha256=row['source_after_sha256'], expected=source_hashes.get(module)))
        raw_log = resolve_input(evidence, row['log'])
        if not raw_log.exists():
            issues['missing_logs'].append(dict(module=module, path=str(raw_log), results_line=line_number))
            continue
        raw = raw_log.read_bytes()
        text = raw.decode(errors='replace')
        log_fingerprints[str(raw_log)] = sha(raw)
        starts = re.findall(r'(?m)^START (\S+)\s*$', text)
        ends = re.findall(r'(?m)^END (\S+)\s*$', text)
        exits = re.findall(r'(?m)^EXIT (-?\d+)\s*$', text)
        commands = re.findall(r'(?m)^COMMAND (.+)$', text)
        protocol = []
        if starts != [row.get('start')] or ends != [row.get('end')] or exits != [str(row['exit'])]:
            protocol.append('START/END/EXIT markers differ from result row or are duplicated')
        try:
            start = datetime.datetime.fromisoformat(row['start'])
            end = datetime.datetime.fromisoformat(row['end'])
            if end < start:
                protocol.append('end precedes start')
        except (KeyError, ValueError, TypeError):
            protocol.append('invalid result timestamps')
        try:
            command = ast.literal_eval(commands[0]) if len(commands) == 1 else None
            if not isinstance(command, list) or 'scripts/lean_check_tree.sh' not in command or command[-1] != module:
                protocol.append('raw command is not one lean_check_tree.sh call for this module')
        except (ValueError, SyntaxError):
            protocol.append('unparseable raw command')
        if row['exit'] != 0:
            issues['nonzero_results'].append(dict(module=module, exit=row['exit'], results_line=line_number))
        if 'FAIL(' in text and row['exit'] == 0:
            protocol.append('raw FAIL marker contradicts exit zero')
        if protocol:
            issues['log_protocol'].append(dict(module=module, results_line=line_number, issues=protocol))
        module_errors, module_sorries = 0, 0
        for log_line, line in enumerate(text.splitlines(), 1):
            match = DIAGNOSTIC.match(line)
            if not match:
                global_match = GLOBAL_ERROR.match(line)
                if global_match:
                    record = dict(module=module, severity='error', code=global_match[1],
                        message=global_match[2], diagnostic_file=None, line=None, column=None,
                        raw_log=str(raw_log), raw_log_line=log_line)
                    all_diagnostics.append(record)
                    issues['error_diagnostics'].append(record)
                    module_errors += 1
                continue
            file, lineno, column, severity, code, message = match.groups()
            record = dict(module=module, severity=severity, code=code, message=message,
                diagnostic_file=file, line=int(lineno), column=int(column),
                raw_log=str(raw_log), raw_log_line=log_line)
            all_diagnostics.append(record)
            same_module = file.replace('\\', '/').endswith(module + '.lean')
            if not same_module:
                issues['cross_module_diagnostics'].append(record)
            if severity == 'error':
                issues['error_diagnostics'].append(record)
                module_errors += 1
            if severity != 'warning' or not SORRY.search(message):
                continue
            module_sorries += 1
            candidates = [(n, name) for n, name in declarations.get(module, []) if n <= int(lineno)]
            if not same_module or not candidates or not candidates[-1][1]:
                issues['unmapped_sorry_warnings'].append(record)
                continue
            decl_line, name = candidates[-1]
            admissions.append(dict(module=module, declaration=name, line=int(lineno),
                declaration_start_line=decl_line, raw_log=str(raw_log), raw_log_line=log_line,
                results_line=line_number, source_sha256=fingerprints[module],
                resolution='exact_declaration_line' if decl_line == int(lineno) else 'containing_declaration'))
        module_results.append(dict(module=module, results_line=line_number, exit=row['exit'],
            error_diagnostics=module_errors, sorry_warnings=module_sorries,
            per_run_source_sha256=row.get('source_sha256'),
            raw_log=str(raw_log), raw_log_sha256=sha(raw)))

    final_keys = [(row['module'], row['declaration']) for row in admissions]
    counts = Counter(final_keys)
    issues['duplicate_sorry_warnings'] = [dict(module=m, declaration=d, warnings=count)
        for (m, d), count in sorted(counts.items()) if count > 1]
    removed, added = set(baseline_keys) - set(final_keys), set(final_keys) - set(baseline_keys)
    missing_expected = wanted - set(final_keys)
    if len(final_keys) != 21 or set(final_keys) != wanted or removed != {TARGET} or added:
        issues['admission_difference'].append(dict(expected_count=21, actual_warning_count=len(final_keys),
            actual_declaration_count=len(set(final_keys)), removed=serialize_keys(removed),
            added=serialize_keys(added), missing_expected=serialize_keys(missing_expected)))
    passed = not any(issues.values())
    report = dict(status='PASS' if passed else 'FAIL', compiler_invoked=False,
        expected_modules=len(expected), module_result_rows=len(rows),
        unique_checked_modules=len(by_module), baseline_count=len(baseline_keys),
        final_admission_warning_count=len(final_keys), final_admission_declaration_count=len(set(final_keys)),
        expected_only_removal=dict(module=TARGET[0], declaration=TARGET[1]),
        source_pin_note='Current source bytes must match the separately prepared final order audit; per-run source hashes are also checked when recorded by the sweep runner.',
        removed=serialize_keys(removed), added=serialize_keys(added), issues=issues,
        input_files={label: dict(path=str(path), sha256=sha(path.read_bytes())) for label, path in inputs.items()},
        source_sha256=fingerprints, raw_log_sha256=log_fingerprints,
        module_results=module_results)
    for name, value in [('report.json', report), ('admissions.json', admissions), ('diagnostics.json', all_diagnostics)]:
        (output / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    summary = [f"Final sweep comparison: {report['status']}",
        f"Modules: {len(by_module)} unique results / {len(expected)} expected; {len(rows)} result rows.",
        f"Admissions: {len(baseline_keys)} baseline -> {len(set(final_keys))} final declarations ({len(final_keys)} warnings).",
        'Expected sole removal: Authentication.lamport_oneTimeSecure.',
        'Issue groups: ' + ', '.join(f'{name}={len(items)}' for name, items in issues.items() if items)]
    (output / 'SUMMARY.txt').write_text('\n'.join(summary) + '\n')
    print('\n'.join(summary))
    print(str(output / 'report.json'))
    return 0 if passed else 1


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--evidence', required=True)
parser.add_argument('--order', required=True)
parser.add_argument('--order-audit', required=True)
parser.add_argument('--results', required=True)
parser.add_argument('--baseline', default='logs/baseline-admissions.json')
parser.add_argument('--issued', default='inputs/base-sorries.txt')
parser.add_argument('--output', required=True)
sys.exit(main(parser.parse_args()))
