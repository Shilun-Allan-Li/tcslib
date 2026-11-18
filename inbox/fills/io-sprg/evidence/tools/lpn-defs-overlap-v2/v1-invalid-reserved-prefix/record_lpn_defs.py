"""ROOT REVIEW ONLY: immutable paired exact-statement records; never invokes Lean.
Unlike record_overlap.py, the qualification explicitly admits audited LPN.Defs.
"""
from pathlib import Path
import argparse, hashlib, json, re, shutil
WORKTREE = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
PACKET = Path('/private/tmp/io-sprg-proof-notes/M4LPNPrepared')
EXPECTED_INDEX_SHA256 = 'e39bcd9ebaa32c15ff3433d69b3e113f46a29d159b9a6a764d7bb61f150f1489'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def classify(mode, run, text):
    observed = any(line.strip() == 'LPN_DEFS_GUARD_OK_10' for line in text.splitlines())
    flags = {
        'runtime_target_absence_marker': observed,
        'target_present': 'LPN_DEFS_TARGET_PRESENT' in text,
        'heartbeat_timeout': any(t in text for t in
            ('maximum number of heartbeats', '(deterministic) timeout')),
        'exact_no_close': '`exact?` could not close' in text,
        'apply_no_hit': "apply? didn't find any relevant lemmas" in text,
        'unknown_scope': 'unknown namespace' in text or 'unknown scoped' in text,
        'statement_error': any(t in text for t in ('unknown constant', 'Unknown constant',
            'unknown identifier', 'Unknown identifier', 'invalid field', 'type mismatch',
            'Application type mismatch', 'unexpected token', 'failed to synthesize')),
        'unsolved_goals': 'unsolved goals' in text,
    }
    if flags['target_present']:
        status = 'INVALID_IMPORTED_TARGET'
    elif not observed:
        status = 'IMPORT_GUARD_NOT_OBSERVED'
    elif run['rc'] == run['errors'] == run['sorry'] == 0:
        status = 'CLOSED'
    elif mode == 'apply' and run['rc'] == run['errors'] == 0 and run['sorry']:
        status = 'PARTIAL_NOT_PROOF'
    elif flags['unknown_scope']:
        status = 'INVALID_SCOPE'
    elif flags['statement_error']:
        status = 'INVALID_ELABORATION'
    elif flags['heartbeat_timeout']:
        status = 'BOUNDED_HEARTBEAT_TIMEOUT'
    elif flags['exact_no_close']:
        status = 'NO_CLOSING_PROOF'
    elif flags['apply_no_hit']:
        status = 'CLEAN_APPLY_NO_HIT'
    elif flags['unsolved_goals']:
        status = 'PARTIAL_SUGGESTION_NOT_PROOF'
    else:
        status = 'DIAGNOSTIC_REQUIRES_REVIEW'
    return status, flags


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('goal', type=int, choices=range(1, 11))
    ap.add_argument('--tag', required=True)
    ap.add_argument('--reuse', required=True, help='Actual public API used or proposed; not a search result')
    ap.add_argument('--packet', type=Path, default=PACKET)
    a = ap.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_]+', a.tag):
        raise RuntimeError('Use the same immutable tag as the paired root invocations')
    packet = a.packet.resolve()
    index_path = packet / 'overlap/exact-probe-index.json'
    if sha(index_path) != EXPECTED_INDEX_SHA256:
        raise RuntimeError('The exact-statement index differs from root review')
    index = json.loads(index_path.read_text())
    row = next(r for r in index if r['index'] == a.goal)
    stem = Path(row['template']).name.removesuffix('.lean.template')
    name = 'M4LPNDefs_' + a.tag + '_' + stem
    home = WORKTREE / 'evidence/overlap'
    out = home / 'probes' / name
    if out.exists():
        raise RuntimeError('Preserve immutable records; use a fresh tag')
    records = [json.loads(line) for line in (home / 'runs/results.jsonl').read_text().splitlines()]
    prepared = []
    for mode in ('exact', 'apply'):
        directory = home / 'root-review-lpn-defs/requests' / name / mode
        request_file = directory / 'request.json'
        completion_file = directory / 'completion.json'
        request, completion = json.loads(request_file.read_text()), json.loads(completion_file.read_text())
        if completion['request_sha256'] != sha(request_file):
            raise RuntimeError('Immutable request/completion binding differs')
        if request['index_sha256'] != EXPECTED_INDEX_SHA256 or request['header_sha256'] != row['header_sha256']:
            raise RuntimeError('Probe statement/header binding differs')
        source = Path(request['source'])
        log = home / 'runs/mods' / (request['module'].replace('/', '_') + '.log')
        run = next(r for r in reversed(records) if r.get('module') == request['module'])
        if run != completion['run'] or run['source_sha256'] != sha(source):
            raise RuntimeError('Runner/source/completion mismatch')
        if request['source_sha256'] != sha(source) or run['log_sha256'] != sha(log):
            raise RuntimeError('Source or log hash mismatch')
        audit_path = directory / 'source-import-audit.json'
        runtime_guard = directory / 'runtime-import-guard.lean.txt'
        if request['source_audit_sha256'] != sha(audit_path):
            raise RuntimeError('Source audit hash mismatch')
        if request['runtime_import_guard_sha256'] != sha(runtime_guard):
            raise RuntimeError('Runtime guard hash mismatch')
        audit = json.loads(audit_path.read_text())
        if audit['target_declarations_found'] or audit['target_leaf_code_occurrences']:
            raise RuntimeError('A target entered the source import closure')
        if not completion['global_guard_unchanged']:
            raise RuntimeError('Global overlap guard mutation was reported')
        text = log.read_text()
        status, flags = classify(mode, run, text)
        diagnostics = [line for line in text.splitlines()
                       if re.match(r'^\S+\.lean:\d+:\d+: error[:(]', line)]
        summary = {'mode': mode, 'status': status, 'diagnostic_flags': flags,
            'runtime_target_absence_observed': flags['runtime_target_absence_marker'],
            'run': run, 'diagnostic_error_headers': diagnostics,
            'request_sha256': sha(request_file), 'request': str(request_file),
            'source_import_audit_sha256': sha(audit_path),
            'audited_owned_import': audit['allowed_project_import'],
            'global_overlap_guard_unchanged': completion['global_guard_unchanged']}
        prepared.append((mode, source, log, summary, request, audit))
    out.mkdir(parents=True, exist_ok=False)
    for mode, source, log, _, request, _ in prepared:
        shutil.copy2(source, out / (mode + '.lean.txt'))
        shutil.copy2(log, out / (mode + '.log'))
        (out / (mode + '-request.json')).write_text(json.dumps(request, indent=2) + '\n')
    summaries = [r[3] for r in prepared]
    result = {'goal': name, 'exact_statement_fullname': row['name'], 'reused_api': a.reuse,
        'qualification': 'ROOT-REVIEWED EXACT-STATEMENT EXCEPTION: these probes import the '
            'audited algorithms-only StructuredSeed.Reductions.LPN.Defs, not all-owned-free '
            'public cores. Current source closure is validated; actual Lean target absence '
            'is claimed only where the explicit ten-name runtime marker is observed. '
            'Transport/Sections/Hop/facade/Security/Targets are excluded. Global overlap_step.py '
            'is unchanged. Search closure is not an owner-proof or axiom audit; partial '
            'suggestions, clean no-hits and bounded timeouts establish no lemma-absence claim.',
        'searches': summaries, 'template_sha256': row['template_sha256'],
        'header_sha256': row['header_sha256'], 'adapter_sha256': sha(Path(__file__)),
        'paired_Defs_olean_hashes_equal': prepared[0][4]['Defs_olean_sha256'] == prepared[1][4]['Defs_olean_sha256'],
        'paired_import_source_bindings_equal': prepared[0][5]['source_sha256'] == prepared[1][5]['source_sha256']}
    (out / 'search.json').write_text(json.dumps(result, indent=2) + '\n')
    with (WORKTREE / 'evidence/lean_proof/search_log.md').open('a') as f:
        f.write('\n' + name + ': ' + ', '.join(r['mode'] + '=' + r['status'] for r in summaries)
                + '. Root-reviewed algorithms-only LPN.Defs import; ten-name runtime guard. '
                + 'Reuse: ' + a.reuse + '.\n')
    print('ROOT_LPN_DEFS_PAIR_RECORDED', name, [r['status'] for r in summaries])
    invalid = {'INVALID_IMPORTED_TARGET', 'IMPORT_GUARD_NOT_OBSERVED', 'INVALID_SCOPE',
               'INVALID_ELABORATION', 'DIAGNOSTIC_REQUIRES_REVIEW'}
    if any(r['status'] in invalid for r in summaries):
        raise SystemExit('Retained invalid/unclassified evidence; repair and use a fresh tag.')

if __name__ == '__main__':
    main()
