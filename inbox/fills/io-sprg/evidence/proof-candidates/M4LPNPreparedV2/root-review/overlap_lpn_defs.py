"""ROOT REVIEW ONLY: one audited exact-statement LPN.Defs search per invocation.
Default prepares evidence without Lean. Explicit --run uses the unchanged serial/no-o
runner and pinned host slot wrapper. Never edits global overlap_step.py or source.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, re, runpy, subprocess, sys
WORKTREE = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
DEFAULT_PACKET = Path('/private/tmp/io-sprg-proof-notes/M4LPNPrepared')
EXPECTED_GUARD_SHA256 = '1b773733aba8251ef744098b1ff8e0a3a7336f64531d2e460ca99833efa06ae9'
EXPECTED_INDEX_SHA256 = 'e39bcd9ebaa32c15ff3433d69b3e113f46a29d159b9a6a764d7bb61f150f1489'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('goal', type=int, choices=range(1, 11))
    ap.add_argument('mode', choices=('exact', 'apply'))
    ap.add_argument('--tag', required=True, help='Fresh immutable version, e.g. V1')
    ap.add_argument('--packet', type=Path, default=DEFAULT_PACKET)
    ap.add_argument('--run', action='store_true', help='ROOT ONLY: invoke one Lean diagnostic')
    a = ap.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_]+', a.tag):
        raise RuntimeError('Use an alphanumeric/underscore fresh tag')
    packet = a.packet.resolve()
    guard_path = packet / 'root-review/lpn_defs_guard.py'
    index_path = packet / 'overlap/exact-probe-index.json'
    if sha(guard_path) != EXPECTED_GUARD_SHA256 or sha(index_path) != EXPECTED_INDEX_SHA256:
        raise RuntimeError('Root-reviewed guard or exact-statement index changed')
    guard = runpy.run_path(str(guard_path))
    audit = guard['validate'](WORKTREE, packet)
    rows = json.loads(index_path.read_text())
    row = next(r for r in rows if r['index'] == a.goal)
    template = packet / 'overlap/exact-statements' / Path(row['template']).name
    text = template.read_text()
    marker = '\nnamespace '
    if marker not in text:
        raise RuntimeError('Expected the reviewed namespace wrapper')
    runtime_guard = guard['lean_guard']()
    text = text.replace(marker, '\n' + runtime_guard + 'namespace ', 1)
    # Template puts := on its own indented line; the one tactic body is indented4.
    text = text.replace('__PROBE_BODY__', 'by\n    ' + a.mode + '?')
    if len(re.findall(r':=\s*by\b', text)) != 1 or text.count('LPN_DEFS_GUARD_OK_10') != 1:
        raise RuntimeError('Exactly one proof block and one environment guard are required')
    if max(map(len, text.splitlines())) > 100:
        raise RuntimeError('Generated Lean probe exceeds100 characters per line')
    stem = template.name.removesuffix('.lean.template')
    name = 'M4LPNDefs_' + a.tag + '_' + stem
    module = Path('/private/tmp/io-sprg-overlap') / (name + '-' + a.mode)
    source = module.with_suffix('.lean')
    order = WORKTREE / 'evidence/logs' / ('overlap-' + name + '-' + a.mode + '.txt')
    home = WORKTREE / 'evidence/overlap'
    request_dir = home / 'root-review-lpn-defs/requests' / name / a.mode
    if source.exists() or order.exists() or request_dir.exists():
        raise RuntimeError('Preserve history: use a fresh tag; never overwrite a probe')
    olean = WORKTREE / '.lake/io-sprg-oleans' / (guard['ALLOWED'].replace('.', '/') + '.olean')
    if a.run and not olean.is_file():
        raise RuntimeError('Root must first build the algorithms-only Defs module')
    runner = WORKTREE / 'evidence/tools/seal/runner_full.py'
    slot = Path('/private/tmp/io-sprg-tools/lean-slot.sh')
    global_tool = WORKTREE / 'evidence/tools/overlap_step.py'
    request_dir.mkdir(parents=True, exist_ok=False)
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(text)
    order.parent.mkdir(parents=True, exist_ok=True)
    with order.open('x') as f:
        f.write(str(module) + '\n')
    (request_dir / 'source-import-audit.json').write_text(json.dumps(audit, indent=2) + '\n')
    (request_dir / 'runtime-import-guard.lean.txt').write_text(runtime_guard)
    request = {'status': 'PREPARED_NOT_RUN', 'name': name, 'goal': row['name'],
        'index': a.goal, 'mode': a.mode, 'tag': a.tag, 'module': str(module),
        'source': str(source), 'source_sha256': sha(source),
        'template': str(template), 'template_sha256': sha(template),
        'header_sha256': row['header_sha256'], 'index_sha256': sha(index_path),
        'guard_python_sha256': sha(guard_path),
        'runtime_import_guard_sha256': sha(request_dir / 'runtime-import-guard.lean.txt'),
        'source_audit_sha256': sha(request_dir / 'source-import-audit.json'),
        'global_overlap_guard_sha256': sha(global_tool),
        'runner_sha256': sha(runner), 'slot_wrapper_sha256': sha(slot),
        'Defs_olean_sha256': sha(olean) if olean.is_file() else None,
        'prepared_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'qualification': 'Root-reviewed exception for exactly algorithms-only LPN.Defs. '
            'Global overlap import guard is unchanged. Source-closure audit is static; '
            'the Lean runtime marker must be observed before reporting target absence. '
            'This is an exact-statement diagnostic, not a final owner/axiom proof.'}
    request_path = request_dir / 'request.json'
    request_path.write_text(json.dumps(request, indent=2) + '\n')
    if not a.run:
        print('PREPARED_NOT_RUN', source, 'Use a fresh tag for the later --run invocation.')
        return
    command = [sys.executable, '-I', str(runner), str(WORKTREE), str(order),
               str(WORKTREE / '.lake/io-sprg-oleans'), str(home / 'runs')]
    subprocess.run(command, cwd=WORKTREE, check=True)
    if sha(global_tool) != request['global_overlap_guard_sha256']:
        raise RuntimeError('Global guard changed during this diagnostic; preserve results for review')
    results = [json.loads(line) for line in (home / 'runs/results.jsonl').read_text().splitlines()]
    record = next(r for r in reversed(results) if r.get('module') == str(module))
    if record['source_sha256'] != request['source_sha256']:
        raise RuntimeError('Runner source hash mismatch')
    completion = {'status': 'RUNNER_RETURNED_NOT_PROOF_CLASSIFICATION', 'run': record,
        'request_sha256': sha(request_path),
        'global_guard_unchanged': True, 'record_adapter_required': True}
    (request_dir / 'completion.json').write_text(json.dumps(completion, indent=2) + '\n')
    print('ROOT_DIAGNOSTIC_FINISHED', name, a.mode, 'Record the pair separately.')

if __name__ == '__main__':
    main()
