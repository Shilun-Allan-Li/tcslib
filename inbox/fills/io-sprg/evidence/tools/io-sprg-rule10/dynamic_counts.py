"""io-sprg Mac Rule10 exact runtime-record checker, 2026-11-18; read-only.

Usage: python3 -I dynamic_counts.py ARCHIVED_TOOLS RUN_DIR OUT_JSON
         [--require-complete] [--require-canonical-pass]
RUN_DIR contains seals/{strict-A,strict-B,coe-A,coe-B}, controls/, seal-runs/,
and control-runs/.  This checks generated chunk payloads against frozen JSON
request rows, then exact runtime Name/component/mask/install/EOF coverage.
It invokes neither Lean nor subprocesses and never changes a probe or source.
Host root: /Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange.
"""
import argparse, hashlib, importlib.util, json, re, sys, runpy
from pathlib import Path
sys.dont_write_bytecode = True
ap = argparse.ArgumentParser()
ap.add_argument('tools'); ap.add_argument('run'); ap.add_argument('output')
ap.add_argument('--require-complete', action='store_true')
ap.add_argument('--require-canonical-pass', action='store_true')
ap.add_argument('--environment-tree')
a = ap.parse_args(); run = Path(a.run).resolve()
sp = importlib.util.spec_from_file_location('iosprg_record_adapter',
    Path(a.tools) / 'request_payload_adapter.py')
ad = importlib.util.module_from_spec(sp); sp.loader.exec_module(ad)
sha = lambda b: hashlib.sha256(b).hexdigest()
bind = runpy.run_path(str(Path(__file__).with_name('environment_binding.py')))
environment = bind['snapshot'](a.environment_tree,run) if a.environment_tree else None

def need(ok, message):
    if not ok: raise RuntimeError(message)

def result_map(folder):
    path = folder / 'results.jsonl'; out = {}
    if path.exists():
        for line in path.read_text().splitlines():
            row = json.loads(line)
            if 'module' in row: out[row['module']] = row
    return out

HEADER = re.compile(r'^/- G06-HARNESS (INSTALL|EOF-VERIFY) (\S+) -/', re.M)
COMPONENT = re.compile(r'^  let componentPayload : String := (".*")$', re.M)
COUNT = re.compile(r'^  let expectedRequests : Nat := (\d+)$', re.M)
ERROR = re.compile(r'^\S+\.lean:(\d+):\d+: error[:(]', re.M)

def chunks(probe, rows, label):
    """The generated payload itself, not an assumed CHUNK flag, fixes chunks."""
    headers = list(HEADER.finditer(probe)); phases = {'INSTALL': [], 'EOF-VERIFY': []}
    need(headers, 'missing generated harness headers')
    for ix, h in enumerate(headers):
        block = probe[h.end():headers[ix+1].start() if ix+1 < len(headers) else len(probe)]
        c = COMPONENT.search(block); n = COUNT.search(block)
        need(c is not None and n is not None, 'missing exact generated chunk payload/count')
        payload = json.loads(c[1]); matrix = [r.split('\t') for r in payload.split('\n')] if payload else []
        need(all(len(r) == 6 for r in matrix), 'malformed generated component payload')
        need(int(n[1]) == len(matrix), 'serialized request/component count differs')
        phases[h[1]].append((h[2], matrix))
    need(phases['INSTALL'] == phases['EOF-VERIFY'], 'install/EOF chunk payloads differ')
    expected = [[r['spelling'], ad.canonical(r['name_components']),
        ad.canonical(r['home_components']), str(r['instance']).lower(),
        str(r['matcher']).lower(), str(r['abbrev']).lower()] for r in rows]
    actual = [r for _, matrix in phases['INSTALL'] for r in matrix]
    need(actual == expected, 'chunk request rows do not equal complete frozen request rows')
    used = set(); out = []; at = 0
    for lab, matrix in phases['INSTALL']:
        need(lab == label or re.fullmatch(re.escape(label) + r'_part[1-9][0-9]*', lab),
            'unexpected generated chunk label')
        need(lab not in used, 'duplicate generated chunk label'); used.add(lab)
        out.append((lab, rows[at:at+len(matrix)])); at += len(matrix)
    return out

def record_rows(text, marker, label):
    prefix = marker + ' label=' + label + ' '
    return [line[line.index(prefix):] for line in text.splitlines() if prefix in line]

def verify_records(text, expected):
    expected_labels = {label for label, _ in expected}
    seen_labels = set()
    for line in text.splitlines():
        m = re.search(r'G06-(?:COMPONENT|NAME|MASK|SEAL|SEAL-END) label=(\S+)', line)
        if m: seen_labels.add(m[1])
    need(seen_labels == expected_labels, 'runtime success-record label set differs')
    for label, rows in expected:
        for marker, verifier in [('G06-COMPONENT', ad.verify_component_log),
                                 ('G06-MASK', ad.verify_mask_log)]:
            relevant = '\n'.join(record_rows(text, marker, label))
            verifier(relevant, label, rows, ('install', 'eof'))
        records = record_rows(text, 'G06-NAME', label); found = {}
        for line in records:
            tail = line.split(' spelling=', 1)[1]
            spelling, tail = tail.split(' actual=', 1)
            actual, tail = tail.split(' home=', 1)
            home, tail = tail.rsplit(' before=', 1)
            before, installed = tail.rsplit(' installed=', 1)
            need(spelling not in found, 'duplicate runtime name installation record')
            need(actual == spelling, 'runtime actual Name spelling differs')
            need(before in {'Lean.ReducibilityStatus.reducible',
                'Lean.ReducibilityStatus.semireducible', 'Lean.ReducibilityStatus.irreducible'},
                'unexpected before status')
            need(installed == 'Lean.ReducibilityStatus.irreducible', 'runtime status not irreducible')
            found[spelling] = home
        need(found == {r['spelling']: r['home'] for r in rows},
            'runtime installed-name/home set differs from exact request set')
        install = record_rows(text, 'G06-SEAL', label)
        eof = record_rows(text, 'G06-SEAL-END', label)
        need(len(install) == len(eof) == 1, 'missing/duplicate install/EOF summary')
        m = re.fullmatch(re.escape('G06-SEAL label=' + label) +
            r' requested=(\d+) active=(\d+) already_irreducible=(\d+) verified=(\d+)', install[0])
        need(m is not None, 'malformed install summary')
        need(int(m[1]) == int(m[4]) == len(rows) and int(m[2])+int(m[3]) == len(rows),
            'install summary counts differ')
        need(eof[0] == f'G06-SEAL-END label={label} requested={len(rows)} verified={len(rows)}',
            'EOF summary counts differ')

seals = {}; results = []; failures = []
for variant in sorted((run / 'seals').iterdir()):
    if not variant.is_dir(): continue
    manifest = json.loads((variant / 'manifest.json').read_text())
    for brief in manifest['probes']:
        rec = json.loads((variant / (brief['label'] + '.json')).read_text())
        need(rec['requested'] == len(rec['rows']) == brief['requested'], 'manifest request count differs')
        seals[variant.name, rec['module']] = rec
        results.append(('seal', variant.name, rec, variant / (rec['label'] + '.lean.txt')))
for variant in sorted((run / 'controls').iterdir()) if (run / 'controls').exists() else []:
    if not variant.is_dir(): continue
    for plan in json.loads((variant / 'controls-plan.json').read_text()):
        results.append(('control', variant.name, plan, variant / (plan['label'] + '.lean.txt')))
lookup = {kind: result_map(run / (kind + '-runs')) for kind in ('seal', 'control')}
report = []
for kind, variant, rec, source in results:
    module = rec['probe_module'] if kind == 'seal' else rec['module']
    row = dict(kind=kind, variant=variant, module=module, requested=rec['requested'])
    rr = lookup[kind].get(module)
    if rr is None:
        row['status'] = 'NOT_RUN'; report.append(row); continue
    try:
        original = source.read_bytes()
        expected_sha = rec['probe_sha256'] if kind == 'seal' else rec['source_sha256']
        need(sha(original) == expected_sha == rr['source_sha256'], 'probe bytes/run hash differ')
        if environment:
            bound = bind['previous'](run / (kind + '-environment-bindings.jsonl'),module)
            need(bound is not None and bound['environment_sha256'] == environment, 'missing/current import environment binding differs')
            need(bound['source_sha256'] == rr['source_sha256'] and bound['log_sha256'] == rr['log_sha256'], 'environment binding does not identify this exact run')
        logfile = run / (kind + '-runs') / 'mods' / (module.replace('/', '_') + '.log')
        logbytes = logfile.read_bytes(); text = logbytes.decode('utf-8')
        need(sha(logbytes) == rr['log_sha256'], 'runtime log hash differs')
        errors = [int(m[1]) for m in ERROR.finditer(text)]
        need(len(errors) == rr['errors'], 'runner/independent standard error counts differ')
        need(text.count('error') == rr['error_substr'], 'runner/independent substring error counts differ')
        sealed = kind == 'seal' or rec['sealed']
        if sealed:
            seal = rec if kind == 'seal' else seals[variant, rec['owner']]
            need(rec['requested'] == len(seal['rows']), 'control/full-owner request count differs')
            cs = chunks(original.decode('utf-8'), seal['rows'], rec['label'])
            verify_records(text, cs)
            row['chunks'] = len(cs)
        if kind == 'control':
            occupied = set()
            for ctl in rec['controls']:
                inside = [e for e in errors if ctl['start_line'] <= e <= ctl['end_line']]
                want = 1 if rec['sealed'] and ctl['negative'] else 0
                need(len(inside) == want, f'control {ctl["control"]}: expected {want} errors, got {len(inside)}')
                occupied.update(inside)
            need(len(occupied) == len(errors), 'stray control diagnostic outside declarations')
            want_rc = 1 if rec['sealed'] and any(c['negative'] for c in rec['controls']) else 0
            need(rr['rc'] == want_rc, 'control return code differs from expected negatives')
        row.update(status='PASS_RECORDS', rc=rr['rc'], errors=len(errors),
            error_substr=rr['error_substr'], seconds=rr.get('seconds'))
    except Exception as error:
        row.update(status='FAIL_RECORDS', reason=str(error)); failures.append(row)
    report.append(row)
pending = [r for r in report if r['status'] == 'NOT_RUN']
canonical_bad = [r for r in report if r['kind'] == 'seal' and r['variant'].startswith('coe-')
    and r['status'] == 'PASS_RECORDS' and (r['rc'] != 0 or r['errors'] != 0 or r['error_substr'] != 0)]
out = dict(records_all_ok=not failures, complete=not pending, canonical_pass=not canonical_bad,
    environment_sha256=environment, planned=len(report), completed=sum(r['status'] != 'NOT_RUN' for r in report),
    failures=failures, canonical_bad=canonical_bad, probes=report,
    qualification='Runtime record checks only; strict source diagnostics remain attributed by sealsum.')
Path(a.output).parent.mkdir(parents=True, exist_ok=True)
Path(a.output).write_text(json.dumps(out, indent=1) + '\n')
print('probes', len(report), 'completed', out['completed'], 'record failures', len(failures),
    'pending', len(pending), 'canonical diagnostics', len(canonical_bad))
if failures or (a.require_complete and pending) or (a.require_canonical_pass and canonical_bad):
    sys.exit(1)
