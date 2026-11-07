"""Validate one optional native kind catalog and prepare TSV; never launches Lean or a scan.

Root must review this source before use. Usage: ATTEMPT_DIRECTORY NEW_IGNORED_OUTPUT.
The hardened Gate04 source scanner remains a separate, reviewed root invocation.
"""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys

HERE = Path(__file__).resolve().parent
MANIFEST_SHA = '1556043af36cb56ec5d5da2438b46b023a603bd4e78a868bf69ec92adb493602'

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def unique(pairs):
    value = {}
    for key, item in pairs:
        need(key not in value, 'duplicate JSON key: ' + key)
        value[key] = item
    return value

def load(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique)

def main():
    need(len(sys.argv) == 3, 'usage: ATTEMPT_DIRECTORY NEW_IGNORED_OUTPUT')
    attempt, output = (Path(p).resolve() for p in sys.argv[1:])
    manifest_raw = (HERE / 'final-explicit-catalog-manifest.json').read_bytes()
    need(sha(manifest_raw) == MANIFEST_SHA, 'reviewed catalog manifest changed')
    m = json.loads(manifest_raw, object_pairs_hook=unique)
    root, label = Path(m['root']), m['label']
    need(output.is_relative_to(root / '.lake/ps-maintainer/gate06') and not output.exists(),
         'output must be fresh ignored Gate06 scratch')
    need(subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'],
         env={**os.environ, 'GIT_OPTIONAL_LOCKS': '0'}).decode().strip() == m['head'], 'HEAD changed')
    full = (HERE / m['full_library_sha_list']).read_bytes()
    need(sha(full) == m['full_library_sha_list_sha256'], 'reviewed full library SHA list changed')
    paths = set()
    for line in full.decode().splitlines():
        digest, rel = line.split('  ', 1)
        paths.add(rel)
        need(sha((root / rel).read_bytes()) == digest, 'library source changed: ' + rel)
    need(paths == {p.relative_to(root).as_posix() for p in (root / 'TCSlib').rglob('*.lean')} |
         {'TCSlib.lean'}, 'library source set changed')
    for path, digest in [(m['scanner'], m['scanner_sha256']),
                         (str(Path(m['scanner']).with_name('declx.py')), m['scanner_declx_sha256'])]:
        need(sha(Path(path).read_bytes()) == digest, 'reviewed scanner/helper changed')
    source = (HERE / 'final-explicit-catalog.source.txt').read_bytes()
    need(sha(source) == m['catalog_source_sha256'] and
         (root / (m['probe_module'] + '.lean')).read_bytes() == source and
         (attempt / (label + '.source.txt')).read_bytes() == source, 'catalog source copies differ')
    result = load(attempt / (label + '.json'))
    log_raw = (attempt / (label + '.log')).read_bytes()
    log = log_raw.decode()
    need(result['rc'] == 0 and result['label'] == label and result['module'] == m['probe_module'] and
         result['source_sha256'] == sha(source) and result['source_unchanged'] is True and
         result['fresh_nonempty_object'] is True and result['error_diagnostics'] == 0,
         'catalog is not a completed fresh native success')
    need(not re.search(r'\.lean:\d+:\d+: error(?:\([^\n)]*\))?:', log), 'catalog contains an error')
    need(re.findall(r'(?m)^START (\S+)\s*$', log) == [result['start']] and
         re.findall(r'(?m)^SOURCE_SHA256 ([0-9a-f]{64})\s*$', log) == [sha(source)] and
         re.findall(r'(?m)^END (\S+) RC (-?\d+)\s*$', log) == [(result['end'], '0')] and
         log.rstrip().endswith('RC 0'), 'catalog completion markers differ')
    obj = Path(m['olean_tree']) / (m['probe_module'] + '.olean')
    need(obj.is_file() and not obj.is_symlink() and obj.stat().st_size > 0 and
         sha(obj.read_bytes()) == result['object_sha256'] and
         obj.stat().st_mtime >= datetime.datetime.fromisoformat(result['start']).timestamp(),
         'missing, stale, or changed catalog object')
    rows, markers, locations = [], {}, []
    stem = f"base={m['base']} head={m['head']} modules={m['expected_math_modules']} rows="
    for number, raw in enumerate(log.splitlines(), 1):
        line = re.sub(r'^.*?\.lean:\d+:\d+: info: ', '', raw)
        if line.startswith('G06-EXPLICIT-KIND\t'):
            fields = line.split('\t')
            need(len(fields) == 4 and all(fields[1:]), 'malformed catalog row')
            rows.append(fields[1:]); locations.append(number)
        for phase in ('BEGIN', 'END'):
            prefix = 'G06-EXPLICIT-CATALOG-' + phase + ' ' + stem
            if line.startswith(prefix):
                need(phase not in markers and line[len(prefix):].isdigit(), 'malformed/duplicate catalog marker')
                markers[phase] = (number, int(line[len(prefix):]))
    need(set(markers) == {'BEGIN', 'END'} and rows and
         markers['BEGIN'][0] < min(locations) <= max(locations) < markers['END'][0] and
         markers['BEGIN'][1] == markers['END'][1] == len(rows), 'incomplete catalog rows/markers')
    need(len({row[0] for row in rows}) == len(rows), 'duplicate printed actual Name')
    need(all(row[1] in {'def-private', 'def-aux', 'def-proj', 'def-instance', 'def-reducible',
         'def-irreducible', 'def', 'thm', 'axiom', 'opaque', 'quot', 'inductive', 'ctor', 'rec'}
         for row in rows), 'unknown/missing declaration kind')
    native_table = ''.join('\t'.join(row) + '\n' for row in rows).encode()
    # The legacy scanner ignores these data-definition subclasses. Broaden its
    # labels without losing any name/home; preserve the exact native table too.
    broaden = {'def-private', 'def-aux', 'def-proj', 'def-irreducible'}
    scan_rows = [[name, 'def' if kind in broaden else kind, home] for name, kind, home in rows]
    table = ''.join('\t'.join(row) + '\n' for row in scan_rows).encode()
    validation = {'status': 'NATIVE_KIND_CATALOG_VERIFIED_SCAN_NOT_RUN', 'base': m['base'], 'head': m['head'],
         'rows': len(rows), 'table_sha256': sha(table), 'manifest_sha256': sha(manifest_raw),
         'native_kinds_sha256': sha(native_table), 'scanner_kind_broadening': sorted(broaden),
         'source_sha256': sha(source), 'log_sha256': sha(log_raw),
         'result_sha256': sha((attempt / (label + '.json')).read_bytes()),
         'limit': 'No source failure exclusion or explicit-list/implicit-read pass is inferred.'}
    output.mkdir()
    for name, raw in [('native-kinds.tsv', native_table), ('constants.tsv', table), ('catalog-validation.json',
         (json.dumps(validation, indent=2) + '\n').encode())]:
        with (output / name).open('xb') as handle:
            handle.write(raw)
    print(json.dumps(validation))

if __name__ == '__main__':
    main()
