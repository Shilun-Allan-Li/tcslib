"""Fresh Gate06 final seals and all eleven controls; review before execution.

python3 -I /absolute/path/run_gate06_final_native.py run-all --adapter-sha256 REVIEWED_SHA256
run-seals / run-controls also exist, each with one fresh fixed output directory.
No collection, preparation, base-source replay, resume, or retry is implemented.
Importing this file does not launch anything. Root coordinates the sole Lean tree.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
from types import SimpleNamespace


ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
TOOLS = ROOT / '.lake/ps-maintainer/gate06'
SCRATCH_REL = Path('.lake/ps-maintainer/gate06/rule10-final-r1')
EVIDENCE = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1')
OLEANS = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/oleans-gate06-r1')
SETUP = ROOT / 'briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-run/setup-summary.json'
HELPERS = TOOLS / 'repairs/s2_native_seal_driver.py'
CHECKER = TOOLS / 'check_probe_v2.py'
PREPARER = TOOLS / 'repairs/prepare_gate06_final_collector.py'
ADAPTER = TOOLS / 'repairs/prepare_gate06_final.py'
FIXED_SHA = {
    str(HELPERS): '0c58a5d287dd1487dc5bbda47283ad4ab9e3c5fe0ba50e9c902c369df55fa7e8',
    str(CHECKER): '5048912fda9ecd1eb6dd9a238d94bfd73d55a70e9e7d2c4a2df75bfda7e9d146',
    str(SETUP): '4618c1f0290464d44477bf6b493663af3e0a572917fc7088af47db5a18be6de2',
    str(ROOT / 'scripts/lean_check_tree.sh'): '366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335',
    str(ROOT / 'lean-toolchain'): 'dbbf063fc415c8e718172605f23a8f86679a3c320eff6d3890cc009534452925',
    str(ROOT / 'lake-manifest.json'): 'cad7de215c4cc216d03acb77cb1abfbe9f3b4062a8988b29459504f932015100',
    str(PREPARER): 'a402e458b32f65edb272276dfb8b6dd9ed59b992024b586b42ccfebe737470f4',
    str(ADAPTER): '130f92d412ed7d60f3496c3928b06621f1ebde81363ecb5fbb7ff0fc91ccdb54',
}
BUILD_SHA = {
    'build_seals.py': 'fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a',
    'build_controls.py': '484009543d095685b50fea244427adf4907de11bd5ef6a9e17e76fe08c60cf89',
    'request_payload_adapter.py': 'ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de',
}
PREPARATION_SHA = {**BUILD_SHA,
    'prepare_audit.py': '055e652d9769044d757960586a94f4feffe78a942ca2d9555f02db9dccfa258f',
    'touched.py': '95d47b5541adcf4670120ab761890a2be899c3f1e77e367a459cac7ad96ffe97',
    'collect_body.lean': '751aa8f8385a05690a0a0097acaff6d93e7349067b5e16a5a59662db0cafb57b',
    'check_probe_v2.py': FIXED_SHA[str(CHECKER)],
}
NEGATIVES = {'InArg', 'AdvInput', 'Uexp', 'AnonymousOnly', 'Matcher'}
REQUEST_ENCODING = 'constant-AST newline/tab String parsed at runtime'


class FinalDriverError(RuntimeError):
    pass


def require(ok, message):
    if not ok:
        raise FinalDriverError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, f'duplicate JSON key: {key}')
        obj[key] = value
    return obj


def read_json(path):
    obj = json.loads(path.read_bytes(), object_pairs_hook=unique_object)
    require(isinstance(obj, dict), f'expected JSON object: {path}')
    return obj


def load_pinned(path, digest, name):
    require(path.is_file() and not path.is_symlink() and sha(path.read_bytes()) == digest,
            f'changed/non-ordinary reviewed tool: {path}')
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, f'cannot load {path}')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def capture(ctx, path):
    require(path.is_file() and not path.is_symlink(), f'non-ordinary input: {path}')
    raw = path.read_bytes()
    digest = sha(raw)
    require(str(path) not in ctx.inputs or ctx.inputs[str(path)] == digest, f'input changed: {path}')
    ctx.inputs[str(path)] = digest
    return raw


def validate_object(result, module):
    obj = OLEANS / (module + '.olean')
    start = dt.datetime.fromisoformat(result['start']).timestamp()
    require(obj.is_file() and not obj.is_symlink() and obj.stat().st_size > 0 and
            sha(obj.read_bytes()) == result['object_sha256'] and obj.stat().st_mtime >= start,
            f'missing, stale, or changed native object: {obj}')


def effective_library_objects(ctx):
    # Match scripts/lean_check_tree.sh's ordered search path for imported TCSlib objects.
    search = [OLEANS]
    local = ROOT / '.lake/build/lib/lean'
    if local.is_dir():
        search.append(local)
    search += sorted(p for p in (ROOT / '.lake/packages').glob('*/.lake/build/lib/lean') if p.is_dir())
    names = set(ctx.modules)
    names.update(m for deps in ctx.closures.values() for m in deps)
    found = {}
    for module in sorted(names):
        rel = module.replace('.', '/') + '.olean'
        obj = next((p / rel for p in search if (p / rel).is_file()), None)
        require(obj is not None and not obj.is_symlink(), f'missing/non-ordinary effective object: {module}')
        found[module] = {'path': str(obj), 'sha256': sha(obj.read_bytes())}
    return found


def assert_frozen(ctx):
    require(ctx.bs.git(ROOT, 'rev-parse', 'HEAD').decode().strip() == ctx.pins['head'], 'HEAD changed')
    paths = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'TCSlib').rglob('*.lean')} | {'TCSlib.lean'}
    require(paths == set(ctx.library), 'library source set changed')
    for rel, raw in ctx.library.items():
        path = ROOT / rel
        require(path.is_file() and not path.is_symlink() and path.read_bytes() == raw, f'library changed: {rel}')
    for path, digest in ctx.inputs.items():
        p = Path(path)
        require(p.is_file() and not p.is_symlink() and sha(p.read_bytes()) == digest, f'input/tool changed: {path}')
    require(effective_library_objects(ctx) == ctx.library_objects, 'effective imported library objects changed')


def verify_controls(ctx):
    # Same body/catalog/region validation as the reviewed S2 driver, with a dynamic audited module.
    v, m = ctx.v, ctx.controls
    audited = ctx.by_module[m['audited_module']]
    require(m['audited_probe_label'] == audited['label'] and m['import_closure'] == ctx.closures[m['audited_module']],
            'control parent/closure metadata differs')
    for key in ('requested_names', 'requested_count', 'collector_active_candidate_count', 'collector_irreducible_count'):
        require(m[key] == audited[key], f'control closure differs from fresh audited module: {key}')
    require(m['positive_readers'] == ctx.cb.READERS and len(ctx.cb.READERS) == 3, 'reader catalog differs')
    for name, (home, matcher) in ctx.cb.REQUIRED.items():
        row = next((r for r in m['requested_names'] if r['spelling'] == name), None)
        require(row is not None and row['home'] == home and row['matcher'] is matcher and
                row['collector_reducibility'] != 'irreducible' and m['required_negative_targets'][name] == row,
                f'invalid sensitivity target: {name}')
    probes = m['probes']
    cases = {(case, mode) for case in NEGATIVES for mode in ('Unsealed', 'Sealed')} | {('PublishedReaders', 'Sealed')}
    require(len(probes) == 11 == m['expected_totals']['probes'] and
            {(p['case'], p['mode']) for p in probes} == cases and len({p['label'] for p in probes}) == 11,
            'all eleven fresh controls are required')
    for p in probes:
        label = 'G06Control_' + p['case'] + '_' + p['mode']
        require(p['label'] == label and p['status'] == 'PREPARED_NOT_RUN' and
                Path(p['probe_path']) == ROOT / SCRATCH_REL / 'controls' / (label + '.lean') and
                Path(p['saved_source']) == EVIDENCE / 'controls' / (label + '.source.txt'), 'not a fresh canonical control')
        sealed = p['mode'] == 'Sealed'
        errors = int(sealed and p['case'] in NEGATIVES)
        require(p['full_closure_sealed'] is sealed and p['requested_count'] == m['requested_count'] and
                p['expected_error_diagnostics'] == errors and p['expected_harness_errors'] == 0 and
                p['fresh_nonempty_object_required'] is (errors == 0) and
                p['expected_exit'] == ('nonzero' if errors else 0) and
                p['proof_count'] == (3 if p['case'] == 'PublishedReaders' else 1), 'control expectation differs')
        if p['case'] == 'PublishedReaders':
            require(set(p['readers']) == set(ctx.cb.READERS), 'reader control set differs')
        else:
            target = ('Complexity.polyTimeComputable_iterateFind.match_1' if p['case'] == 'Matcher'
                      else ctx.cb.NEGATIVE_BODIES[p['case']][0])
            require(p['target'] == target and p['anonymous_only'] is (p['case'] == 'AnonymousOnly'),
                    'negative target/anonymous flag differs')
        raw = v.capture(ctx, v.probe_path(p))
        require(raw == v.capture(ctx, v.saved_path(p)) and sha(raw) == p['source_sha256'], 'control source differs')
        body = v.expected_control_body(ctx, p)
        region = p['proof_region']
        require(len(region['rfl_lines']) == (0 if p['case'] == 'PublishedReaders' else 1),
                'negative control must have exactly one rfl proof site')
        extracted = b''.join(raw.splitlines(keepends=True)[region['start'] - 1:region['end']])
        require(extracted == body and ('body_sha256' not in p or sha(body) == p['body_sha256']), 'control body differs')
        generated, expected_region = ctx.cb.assemble(ctx.bs, p['label'], m['audited_module'], m['requested_names'],
                                                    body, sealed=sealed)
        require(generated == raw and expected_region == region, 'control is not reproduced by configured builder')


def load_context(adapter_sha):
    require(re.fullmatch('[0-9a-f]{64}', adapter_sha) is not None, 'reviewed adapter SHA256 required')
    ctx = SimpleNamespace(inputs={})
    capture(ctx, Path(__file__).resolve())
    for path, digest in FIXED_SHA.items():
        require(sha(capture(ctx, Path(path))) == digest, f'fixed configuration/tool changed: {path}')
    require(read_json(SETUP)['olean_tree'] == str(OLEANS) and OLEANS.is_dir(), 'not the intended Gate06 olean tree')
    ctx.v = load_pinned(HELPERS, FIXED_SHA[str(HELPERS)], 'gate06_final_pure_validators')
    # Only generic validators are called. S2 load_context/axioms/base/run functions are never used.
    ctx.v.S2_ROOT, ctx.v.SCRATCH, ctx.v.EVIDENCE = ROOT, ROOT / SCRATCH_REL, EVIDENCE
    for name in ('final-adapter.json', 'final-preparation.json', 'pins.json', 'seal-manifest.json',
                 'controls-manifest.json', 'modules.json', 'closures.json', 'source-fingerprints.json', 'touched.json'):
        capture(ctx, EVIDENCE / name)
    require(sha((EVIDENCE / 'final-adapter.json').read_bytes()) == adapter_sha, 'unreviewed final adapter binding')
    ctx.adapter, prep, ctx.pins, ctx.head, ctx.controls = (read_json(EVIDENCE / n) for n in
        ('final-adapter.json', 'final-preparation.json', 'pins.json', 'seal-manifest.json', 'controls-manifest.json'))
    ctx.modules, ctx.closures, fps, touched = (read_json(EVIDENCE / n) for n in
        ('modules.json', 'closures.json', 'source-fingerprints.json', 'touched.json'))
    a, n = ctx.adapter, len(ctx.modules)
    require(n > 0 and a['status'] == ctx.head['status'] == ctx.controls['status'] == 'PREPARED_NOT_RUN', 'not prepared fresh')
    require(prep['status'] == 'COLLECTOR_PREPARED_NOT_RUN' and a['runtime_verified'] is False,
            'unexpected final preparation lifecycle state')
    for obj in (a, prep):
        require(obj['root'] == str(ROOT) and obj['evidence_directory'] == str(EVIDENCE) and
                obj['base'] == ctx.pins['base'] and obj['head'] == ctx.pins['head'] and
                obj['expected_math_modules'] == n and obj['modules'] == sorted(ctx.modules) and
                obj['scratch_relative'] == SCRATCH_REL.as_posix(), 'final preparation scope/pins differ')
    require(a['tool_input_sha256'] == BUILD_SHA and a['request_encoding'] == REQUEST_ENCODING and
            a['proof_budgets_changed'] is False and a['coverage_exclusions_added'] is False,
            'reviewed final adapter configuration differs')
    for field, filename in [('final_preparation_sha256', 'final-preparation.json'),
                            ('seal_manifest_sha256', 'seal-manifest.json'),
                            ('controls_manifest_sha256', 'controls-manifest.json'),
                            ('collector_result_sha256', 'collect1.json')]:
        require(sha(capture(ctx, EVIDENCE / filename)) == a[field], f'unbound final artifact: {filename}')
    require(a['source_sha256'] == FIXED_SHA[str(ADAPTER)] and
            a['preparer_source_sha256'] == prep['preparer_source_sha256'] == FIXED_SHA[str(PREPARER)],
            'unreviewed final preparation code')
    for filename, digest in [('prepare_gate06_final.py', a['source_sha256']),
                             ('prepare_gate06_final_collector.py', prep['preparer_source_sha256'])]:
        require(sha(capture(ctx, EVIDENCE / filename)) == digest, f'preparation source differs: {filename}')
    saved_names = {name: name + '.source.txt' if name.endswith('.lean') else name for name in PREPARATION_SHA}
    require(prep['tool_input_sha256'] == PREPARATION_SHA and prep['tool_saved_names'] == saved_names,
            'preparation tool set/archive names differ')
    for name, digest in PREPARATION_SHA.items():
        require(sha(capture(ctx, EVIDENCE / 'tool-inputs' / saved_names[name])) == digest,
                f'archived preparation tool differs: {name}')
    require(prep['collector_label'] == 'collect1' and
            prep['collector_module'] == (SCRATCH_REL / 'Collect').as_posix(), 'wrong final collector')
    for obj in (prep, ctx.head, ctx.controls):
        for filename, digest in obj['input_sha256'].items():
            require(Path(filename).name == filename, 'unsafe input filename')
            require(sha(capture(ctx, EVIDENCE / filename)) == digest, f'prepared input differs: {filename}')
    tools = {name: load_pinned(EVIDENCE / 'tool-inputs' / name, digest, 'g06_final_' + name.replace('.', '_'))
             for name, digest in BUILD_SHA.items()}
    for name in BUILD_SHA:
        capture(ctx, EVIDENCE / 'tool-inputs' / name)
    ctx.bs, ctx.cb, payload = (tools[name] for name in BUILD_SHA)
    ctx.bs.EXPECTED_MODULES, ctx.bs.SCRATCH_REL = n, SCRATCH_REL
    payload.configure_builders(ctx.bs, ctx.cb)
    require(ctx.head['builder_sha256'] == ctx.controls['seal_builder_sha256'] == BUILD_SHA['build_seals.py'] and
            ctx.controls['builder_sha256'] == BUILD_SHA['build_controls.py'], 'manifest builder hashes differ')
    for filename, digest in [('build_seals.py', BUILD_SHA['build_seals.py']),
                             ('controls-builder.source.txt', BUILD_SHA['build_controls.py'])]:
        require(sha(capture(ctx, EVIDENCE / filename)) == digest, f'archived configured builder differs: {filename}')
    require(ctx.head['notation_exclusions_exact'] == sorted(ctx.bs.NOTATION_EXCLUSIONS), 'notation exclusions differ')
    ctx.library, ctx.snapshot = ctx.bs.library_snapshot(ROOT, ctx.pins)
    ctx.bs.validate_metadata(ROOT, ctx.pins, ctx.modules, ctx.closures, fps, touched, ctx.library)
    for obj in (a, prep, ctx.head, ctx.controls):
        require(obj['library_verification'] == ctx.snapshot, 'library verification differs')
    require(ctx.head['root'] == ctx.controls['root'] == str(ROOT) and
            ctx.head['evidence_directory'] == ctx.controls['evidence_directory'] == str(EVIDENCE), 'manifest root differs')
    require(ctx.controls['seal_manifest_sha256'] == a['seal_manifest_sha256'] and
            ctx.controls['audited_module'] == a['controls_module'] and a['controls_module'] in ctx.modules,
            'controls not bound to the fresh full closure')
    captured = {}
    log, completion, warnings = ctx.bs.completed_collector(ROOT, EVIDENCE, captured, ctx.modules, ctx.closures)
    require(completion == ctx.head['collector_result'] and warnings == ctx.head['warnings'] and
            not ctx.v.diagnostics(log), 'collector completion differs or contains errors')
    for filename, raw in captured.items():
        require(capture(ctx, EVIDENCE / filename) == raw, f'collector input changed: {filename}')
    validate_object(completion, prep['collector_module'])
    terms, closure_rows, ctx.inventory = ctx.bs.collector_rows(log, ctx.modules, ctx.closures)
    require(read_json(EVIDENCE / 'seal-collector-inventory.json') == ctx.inventory, 'collector inventory differs')
    capture(ctx, EVIDENCE / 'seal-collector-inventory.json')
    ctx.by_module = {p['module']: p for p in ctx.head['probes']}
    require(len(ctx.by_module) == len(ctx.head['probes']) == n and set(ctx.by_module) == set(ctx.modules), 'not all N seals')
    require([p['module'] for p in ctx.head['probes']] == sorted(ctx.modules) and
            [p['ordinal'] for p in ctx.head['probes']] == list(range(1, n + 1)), 'fresh seal order differs')
    for p in ctx.head['probes']:
        label = 'G06Seal_' + f'{p["ordinal"]:03d}_' + p['module'].replace('.', '_').replace("'", '_prime')
        require(p['label'] == label and p['status'] == 'PREPARED_NOT_RUN' and p['original_bytes_preserved'] is True and
                Path(p['probe_path']) == ROOT / SCRATCH_REL / 'seals' / (label + '.lean') and
                Path(p['saved_source']) == EVIDENCE / 'seals' / (label + '.source.txt'), 'not a fresh canonical seal')
        require(p['source'] == ctx.modules[p['module']] and p['term_names'] == sorted(terms[p['module']]) and
                p['requested_names'] == [closure_rows[p['module']][k] for k in sorted(closure_rows[p['module']])],
                f'not the complete fresh collected closure: {p["module"]}')
        ctx.v.verify_whole(ctx, p, ctx.library[p['source']])
    verify_controls(ctx)
    ctx.library_objects = effective_library_objects(ctx)
    ctx.adapter_sha = adapter_sha
    assert_frozen(ctx)
    return ctx


def invoke(ctx, p, out):
    # Same result/footer/path/fresh-object checks as S2 invoke, configured for G06.
    assert_frozen(ctx)
    v, path = ctx.v, ctx.v.probe_path(p)
    expected = p.get('probe_sha256', p.get('source_sha256'))
    raw = path.read_bytes()
    require(sha(raw) == expected and raw == Path(p['saved_source']).read_bytes(), 'probe changed before native check')
    attempt = out / 'probes' / p['label']
    attempt.mkdir(parents=True, exist_ok=False)
    print('G06 FINAL START ' + p['label'], flush=True)
    proc = subprocess.run([sys.executable, '-I', str(CHECKER), str(attempt), p['probe_module'], p['label']],
                          cwd=ROOT, capture_output=True, text=True, check=False)
    v.write_new(attempt / 'launcher.log', (proc.stdout + proc.stderr).encode())
    log_path, result_path = attempt / (p['label'] + '.log'), attempt / (p['label'] + '.json')
    record = {'label': p['label'], 'log': str(log_path), 'result_path': str(result_path),
              'head_before_and_after': ctx.pins['head'], 'launcher_returncode': proc.returncode}
    try:
        result_raw, log_raw = result_path.read_bytes(), log_path.read_bytes()
        result = json.loads(result_raw, object_pairs_hook=unique_object)
        text = log_raw.decode()
        record.update(result=result, errors=v.diagnostics(text), warnings=v.diagnostics(text, v.WARNING_RE),
                      result_json_sha256=sha(result_raw), log_sha256=sha(log_raw), captured_probe_sha256=sha(raw))
        require(result['module'] == p['probe_module'] and result['label'] == p['label'] and
                result['source_sha256'] == expected and result['source_unchanged'] is True and
                proc.returncode == result['rc'] and result['rc'] in (0, 1), 'checker result/exit/source differs')
        require((attempt / (p['label'] + '.source.txt')).read_bytes() == raw == path.read_bytes(), 'captured probe differs')
        require(re.findall(r'(?m)^START (\S+)\s*$', text) == [result['start']] and
                re.findall(r'(?m)^SOURCE_SHA256 ([0-9a-f]{64})\s*$', text) == [expected] and
                re.findall(r'(?m)^END (\S+) RC (-?\d+)\s*$', text) == [(result['end'], str(result['rc']))] and
                text.rstrip().endswith('RC ' + str(result['rc'])), 'completion/footer/source marker differs')
        require(len(record['errors']) == result['error_diagnostics'], 'coded/ordinary diagnostic count differs')
        require('G06-HARNESS ' not in text and 'G06-CONTROL-HARNESS ' not in text, 'explicit harness failure')
        for error in record['errors']:
            require((ROOT / error['path']).resolve() == path.resolve(), 'diagnostic belongs to dependency/other file')
        if result['rc'] == 0:
            require(not record['errors'] and result['fresh_nonempty_object'] is True, 'rc0 not a fresh error-free result')
            validate_object(result, p['probe_module'])
        else:
            require(record['errors'] and result['fresh_nonempty_object'] is False and result['object_sha256'] is None,
                    'rc1 is not a located Lean error')
        return record, text
    except (FinalDriverError, v.DriverError, OSError, KeyError, TypeError, ValueError) as error:
        record.update(valid_harness=False, classification='HARNESS_OR_SETUP_FAILURE', harness_reason=str(error))
        return record, None
    finally:
        assert_frozen(ctx)


def classify_seal(ctx, p, record, text):
    v = ctx.v
    install, eof = v.check_installation(text, p['label'], p)
    inverse = {r['probe_line']: r['source_line'] for r in p['source_to_probe_lines']}
    starts = v.source_commands(ctx, ctx.library[p['source']])
    for error in record['errors']:
        require(error['probe_line'] in inverse and install < error['log_line'] < eof,
                'diagnostic is in inserted harness/import setup, not sealed source')
        line = inverse[error['probe_line']]
        error.update(source_line=line, **v.source_location(starts, line), classification='SOURCE_FAILURE_REQUIRES_REVIEW')
    record.update(valid_harness=True, source_failure=bool(record['errors']),
                  classification='SOURCE_FAILURE_REQUIRES_REVIEW' if record['errors'] else 'SEALED_SOURCE_ELABORATED')


def classify_control(ctx, p, record, text):
    v, m = ctx.v, ctx.controls
    n, readers = m['requested_count'], len(m['positive_readers'])
    catalog = v.markers(text, 'G06-CONTROL-CATALOG label=')
    expected_catalog = [f'G06-CONTROL-CATALOG label={p["label"]} phase={phase} requested={n} verified={n} readers={readers}'
                        for phase in (('before',) if p['full_closure_sealed'] else ('before', 'after'))]
    require([line for _, line in catalog] == expected_catalog, 'control catalog differs')
    before = catalog[0][0]
    if p['full_closure_sealed']:
        installed, after = v.check_installation(text, p['label'], m)
        require(before < installed, 'control seal precedes catalog')
    else:
        after = catalog[1][0]
        require(not any(v.markers(text, prefix) for prefix in ('G06-SEAL label=', 'G06-SEAL-END label=', 'G06-NAME label=')),
                'unsealed control unexpectedly installs a seal')
    begin = v.exact_marker(text, 'G06-CONTROL-BODY-BEGIN ', 'G06-CONTROL-BODY-BEGIN ' + p['label'])
    end = v.exact_marker(text, 'G06-CONTROL-BODY-END ', 'G06-CONTROL-BODY-END ' + p['label'])
    require(before < begin < end < after, 'control catalog/body/end order differs')
    if p['full_closure_sealed']:
        require(installed < begin, 'control body precedes complete installation')
    expected_errors = int(p['case'] in NEGATIVES and p['mode'] == 'Sealed')
    require(p['expected_error_diagnostics'] == expected_errors and len(record['errors']) == expected_errors,
            'control diagnostic count differs')
    if expected_errors:
        error = record['errors'][0]
        require(record['result']['rc'] == 1 and error['probe_line'] in p['proof_region']['rfl_lines'] and
                begin < error['log_line'] < end, 'negative failure is not its sole body rfl proof error')
    else:
        require(record['result']['rc'] == 0 and record['result']['fresh_nonempty_object'], 'positive control did not pass')
    record.update(valid_harness=True, expected_outcome=True, classification='CONTROL_VERIFIED')


def run(ctx, kind):
    v = ctx.v
    out = EVIDENCE / ('native-seal-runs' if kind == 'seals' else 'native-control-runs')
    require(not out.exists(), f'no reuse/overwrite of a final run: {out}')
    assert_frozen(ctx)
    out.mkdir()
    v.write_new(out / 'driver.source.txt', Path(__file__).read_bytes())
    for name, path in [('validators.source.txt', HELPERS), ('checker.source.txt', CHECKER),
                       ('lean_check_tree.source.txt', ROOT / 'scripts/lean_check_tree.sh'), ('setup-summary.json', SETUP)]:
        v.write_new(out / name, path.read_bytes())
    config = {'root': str(ROOT), 'evidence_directory': str(EVIDENCE), 'scratch_relative': SCRATCH_REL.as_posix(),
              'olean_tree': str(OLEANS), 'base': ctx.pins['base'], 'head': ctx.pins['head'], 'modules': sorted(ctx.modules),
              'expected_math_modules': len(ctx.modules), 'expected_controls': 11, 'adapter_sha256': ctx.adapter_sha,
              'inputs': ctx.inputs, 'fixed_tool_sha256': FIXED_SHA, 'builder_tool_sha256': BUILD_SHA,
              'preparation_tool_sha256': PREPARATION_SHA,
              'driver_sha256': sha(Path(__file__).read_bytes()), 'library_verification': ctx.snapshot,
              'request_encoding': REQUEST_ENCODING, 'source_base_replays': False, 'previous_attempts_reused': False}
    config_raw = v.json_bytes(config)
    v.write_new(out / 'configuration.json', config_raw)
    v.write_new(out / 'library-object-fingerprints.json', v.json_bytes(ctx.library_objects))
    probes = ctx.head['probes'] if kind == 'seals' else ctx.controls['probes']
    records, aborted = [], None
    try:
        for p in probes:
            record, text = invoke(ctx, p, out)
            record.update(module=p.get('module', ctx.controls['audited_module']), kind=kind)
            if kind == 'controls':
                record.update(case=p['case'], mode=p['mode'], expected_outcome=False)
            if text is not None:
                try:
                    (classify_seal if kind == 'seals' else classify_control)(ctx, p, record, text)
                except (FinalDriverError, v.DriverError, KeyError, TypeError, ValueError) as error:
                    record.update(valid_harness=False, classification='HARNESS_OR_CONTROL_FAILURE' if kind == 'controls'
                                  else 'HARNESS_OR_SETUP_FAILURE', harness_reason=str(error))
            records.append(record)
            v.write_new(out / (p['label'] + '.classification.json'), v.json_bytes(record))
            print(f'G06 FINAL {kind} {len(records)}/{len(probes)} {p["label"]} {record["classification"]}', flush=True)
    except Exception as error:
        aborted = f'{type(error).__name__}: {error}'
    complete = aborted is None and len(records) == len(probes)
    valid = complete and all(r.get('valid_harness') for r in records)
    success = valid and (all(r.get('expected_outcome') for r in records) if kind == 'controls'
                         else not any(r.get('source_failure') for r in records))
    summary = {'kind': kind, 'head': ctx.pins['head'], 'base': ctx.pins['base'], 'expected_probes': len(probes),
               'completed_probes': len(records), 'complete': complete, 'aborted_reason': aborted,
               'uncompleted_labels': [p['label'] for p in probes[len(records):]], 'all_harnesses_valid': valid,
               'success': success, 'status': 'ALL_CONTROLS_VERIFIED' if success and kind == 'controls' else
                    'SEALED_SOURCE_ELABORATED' if success else 'REVIEW_REQUIRED_NO_PASS',
               'harness_failures': sum(not r.get('valid_harness') for r in records),
               'source_error_diagnostics': sum(len(r.get('errors', [])) for r in records if r.get('valid_harness') and kind == 'seals'),
               'configuration_sha256': sha(config_raw), 'results': records,
               'touched_failure_attestation': 'NOT_AUTOMATICALLY_RECONCILED',
               'limit': 'Fresh final epoch only. Every failure is retained; no inherited-source exemption or merge clearance is inferred.'}
    if kind == 'controls':
        summary.update(all_controls_verified=success, anonymous_sensitivity_verified=success,
                       matcher_sensitivity_verified=success, published_readers_verified=success,
                       unsealed_negative_passes=sum(r.get('expected_outcome', False) and r['case'] in NEGATIVES and r['mode'] == 'Unsealed' for r in records),
                       sealed_negative_failures=sum(r.get('expected_outcome', False) and r['case'] in NEGATIVES and r['mode'] == 'Sealed' for r in records),
                       sealed_positive_passes=sum(r.get('expected_outcome', False) and r['case'] == 'PublishedReaders' for r in records))
    v.write_new(out / 'summary.json', v.json_bytes(summary))
    return success


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('run-all', 'run-seals', 'run-controls'))
    parser.add_argument('--adapter-sha256', required=True, help='reviewed SHA256 of fresh final-adapter.json')
    args = parser.parse_args()
    ctx = load_context(args.adapter_sha256)
    kinds = ('seals', 'controls') if args.command == 'run-all' else (args.command.removeprefix('run-'),)
    for kind in kinds:
        require(not (EVIDENCE / ('native-seal-runs' if kind == 'seals' else 'native-control-runs')).exists(),
                'requested final run already exists; no resume/reuse is supported')
    outcomes = [run(ctx, kind) for kind in kinds]  # retain controls even when source seals have ordinary failures
    return 0 if all(outcomes) else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as error:
        print(f'G06-FINAL-NATIVE-FAIL: {type(error).__name__}: {error}', file=sys.stderr, flush=True)
        sys.exit(1)
