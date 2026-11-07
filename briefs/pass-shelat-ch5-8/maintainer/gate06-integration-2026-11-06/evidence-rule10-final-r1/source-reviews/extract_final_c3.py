"""Extract the explicitly reviewed Gate06 C3 R2 census; review before execution.

python3 -I extract_final_c3.py COMPLETED_ATTEMPT NEW_IGNORED_OUTPUT
No subprocesses, Lean, Git commands, helper imports, or evidence updates.
Structural incompleteness creates no output. Missing kind metadata preserves all
pairs in a complete output with a failing review status. Neither outcome clears rule10.
"""
from pathlib import Path
import argparse
import datetime as dt
import hashlib
import json
import re
import sys

ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
G06 = ROOT / '.lake/ps-maintainer/gate06'
HERE = G06 / 'repairs'
E = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1')
HEAD = '3f6db40e1688c4a0bb922c9575dd3bd2157a650b'
BASE = 'eee107e92a7db11f1f8c98a5c2867304f57ddc54'
LABEL = 'G06C3SupplementR2'
MODULE = '.lake/ps-maintainer/gate06/rule10-final-c3-r2/G06C3SupplementR2'
KINDS = HERE / 'final-explicit-native-table-r1/native-kinds.tsv'
SHA_LIST = HERE / 'final-repair-source-review.final.sha256'
SMALL, LOG, TABLE = 4 << 20, 128 << 20, 64 << 20
MAX_PAIRS, MAX_LINE = 1_000_000, 32768
FIXED = {
    HERE / 'final-c3-supplement-r2.source.txt': '26f74568c53a3552173e58c4267c7fcae7108ba562c121f1f2360f0f02c4c2bb',
    HERE / 'final-c3-supplement-r2-manifest.json': 'faa6852a84dd761f2b14dd6b178b9ef524a3876ec9e673e9f602359ced0b53f3',
    HERE / 'final-c3-supplement-r2-notes.md': '8b94aec0d910e46cd06ba5965c8f9fa3b59a0150f335561b1cc7dc6a9d073a30',
    HERE / 'final-explicit-files.txt': 'e027117c0810eabb2cf743e19517ab36ce57ca171a700a510547aaeb966d8d35',
    SHA_LIST: '549c7071cfc76b377738fa7914eaa2bc998104dcdde25c36455d1363736d020a',
    E / 'pins.json': 'f57b6d5a2a5dc202b5fef5a52cd3407dbb3a51cbfee4f62d704b6568e780f6ac',
    E / 'modules.json': 'aaeebbe3c97e2447e5497ce46b0a721816232b861492fd895add6cbda0ebc0f9',
    E / 'axioms-full.json': '81441d20992a14945e7fc8815118e667f1ce7a8e70f6cc4044e2ecfe693dd13d',
    E / 'collect1.json': '7e671fcd21f64a57e8f60fce2dbbf50365121c61e622bc63b4679c4a199fb508',
    E / 'collect1.log': 'f8b1311c6e47f5168dc292fc54ef86835867144c10d0be8ea2da9aa66358285b',
    HERE / 'final-explicit-native-table-r1/catalog-validation.json': '6a4fd3b84d80bd39dc9f73cb069dd3c39a64d80d4cae0d884c8c87e6cf9c31e7',
    KINDS: '7d224439e2954732d11deb19b94150f82cbbbaa978e52985b27e4f0625f2350f',
    G06 / 'check_probe_v2.py': '5048912fda9ecd1eb6dd9a238d94bfd73d55a70e9e7d2c4a2df75bfda7e9d146',
    ROOT / 'briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-run/setup-summary.json': '4618c1f0290464d44477bf6b493663af3e0a572917fc7088af47db5a18be6de2',
    ROOT / 'scripts/lean_check_tree.sh': '366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335',
    ROOT / 'lean-toolchain': 'dbbf063fc415c8e718172605f23a8f86679a3c320eff6d3890cc009534452925',
    ROOT / 'lake-manifest.json': 'cad7de215c4cc216d03acb77cb1abfbe9f3b4062a8988b29459504f932015100',
}
INPUTS = {}
ERROR = re.compile(r'(?m)^.*?\.lean:\d+:\d+: error(?:\([^\n)]*\))?:')
DEF_KINDS = {'def', 'def-private', 'def-aux', 'def-proj', 'def-instance', 'def-reducible', 'def-irreducible'}

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def capture(path, cap=SMALL, expected=None, contents=False):
    need(path.is_file() and not path.is_symlink(), 'non-ordinary/missing input: ' + str(path))
    need(path.stat().st_size <= cap, 'input exceeds explicit size bound: ' + str(path))
    digest, chunks, size = hashlib.sha256(), [], 0
    with path.open('rb') as handle:
        while chunk := handle.read(1 << 20):
            size += len(chunk)
            need(size <= cap, 'input grew beyond size bound: ' + str(path))
            digest.update(chunk)
            if contents:
                chunks.append(chunk)
    value = digest.hexdigest()
    need(expected is None or value == expected, 'input SHA mismatch: ' + str(path))
    need(str(path) not in INPUTS or INPUTS[str(path)]['sha256'] == value, 'input changed: ' + str(path))
    INPUTS[str(path)] = {'sha256': value, 'size': size, 'cap': cap}
    return b''.join(chunks) if contents else value

def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result

def read_json(path):
    value = json.loads(capture(path, contents=True), object_pairs_hook=unique)
    need(isinstance(value, dict), 'expected JSON object: ' + str(path))
    return value

def field(text):
    need(isinstance(text, str) and text and all(ord(c) >= 32 for c in text), 'invalid identity field')
    return text

def check_head():
    # Read Git metadata only; never invoke Git or update the index/refs.
    git = ROOT / '.git'
    if git.is_file():
        line = git.read_text().strip()
        need(line.startswith('gitdir: '), 'invalid worktree Git link')
        git = (ROOT / line[8:]).resolve()
    line = (git / 'HEAD').read_text().strip()
    if line.startswith('ref: '):
        ref = line[5:]
        need(re.fullmatch(r'refs/[A-Za-z0-9._/\-]+', ref) and '..' not in ref.split('/'), 'unsafe HEAD ref')
        common = (git / (git / 'commondir').read_text().strip()).resolve() if (git / 'commondir').is_file() else git
        paths = [p for p in (git / ref, common / ref) if p.is_file()]
        if paths:
            line = paths[0].read_text().strip()
        else:
            packed = common / 'packed-refs'
            need(packed.is_file() and packed.stat().st_size <= SMALL, 'missing/oversized packed refs')
            found = [s.split()[0] for s in packed.read_text().splitlines() if s.endswith(' ' + ref)]
            need(len(found) == 1, 'HEAD ref not uniquely resolved')
            line = found[0]
    need(line == HEAD, 'current HEAD differs from the frozen C3 epoch')

def context():
    check_head()
    capture(Path(__file__).resolve())
    for path, digest in FIXED.items():
        capture(path, TABLE if path == KINDS else LOG if path.name == 'collect1.log' else SMALL, digest)
    m = read_json(HERE / 'final-c3-supplement-r2-manifest.json')
    pins, modules, canon = (read_json(E / n) for n in ('pins.json', 'modules.json', 'axioms-full.json'))
    need(m['root'] == str(ROOT) and m['base'] == pins['base'] == canon['base'] == BASE and
         m['head'] == pins['head'] == canon['head'] == HEAD and m['probe_module'] == MODULE and
         m['native_label'] == LABEL and m['source_sha256'] == FIXED[HERE / 'final-c3-supplement-r2.source.txt'], 'R2 epoch/pin mismatch')
    names = m['modules']
    need(len(names) == len(set(names)) == 54 and names == sorted(modules) and
         modules == {n: n.replace('.', '/') + '.lean' for n in names}, 'not the complete final 54-module scope')
    files = capture(HERE / 'final-explicit-files.txt', contents=True)
    need(sha(files) == m['module_list_sha256'] and files.decode().splitlines() == [modules[n] for n in names],
         'manifest module_list_sha256 must bind the newline source-path list')
    source = capture(HERE / 'final-c3-supplement-r2.source.txt', contents=True)
    need([s.split()[1] for s in source.decode().splitlines() if s.startswith('import TCSlib.')] == names,
         'source imports differ from the final scope')
    source_paths = set()
    for line in capture(SHA_LIST, contents=True).decode().splitlines():
        digest, rel = line.split('  ', 1)
        need(rel == 'TCSlib.lean' or (rel.startswith('TCSlib/') and '..' not in Path(rel).parts), 'unsafe library SHA path')
        need(rel not in source_paths, 'duplicate library SHA path')
        source_paths.add(rel)
        capture(ROOT / rel, TABLE, digest)
    need(len(source_paths) == 1108 and source_paths ==
         {p.relative_to(ROOT).as_posix() for p in (ROOT / 'TCSlib').rglob('*.lean')} | {'TCSlib.lean'}, 'library source set changed')
    collector = read_json(E / 'collect1.json')
    need(collector['rc'] == 0 and collector['error_diagnostics'] == 0 and collector['source_unchanged'] is True and
         collector['fresh_nonempty_object'] is True and canon['collector_log_sha256'] == FIXED[E / 'collect1.log'],
         'canonical identities are not bound to the completed final collector')
    expected = {n: set() for n in names}
    for record in canon['records']:
        mod, name = field(record['module']), field(record['actual_name'])
        need(mod in expected and name not in expected[mod], 'duplicate/out-of-scope canonical identity')
        expected[mod].add(name)
    need(canon['actual_identity_count'] == len(canon['records']) == sum(map(len, expected.values())) == 2881 and
         len(set().union(*expected.values())) == 2881 and all(expected.values()), 'incomplete canonical identity census')
    return m, names, expected, source

def native(attempt, m, source):
    need(attempt.is_dir() and not attempt.is_symlink(), 'missing/non-ordinary native attempt directory')
    result = read_json(attempt / (LABEL + '.json'))
    log = capture(attempt / (LABEL + '.log'), LOG, contents=True).decode()
    need(capture(attempt / (LABEL + '.source.txt'), contents=True) == source ==
         capture(ROOT / (MODULE + '.lean'), contents=True), 'native/current/source snapshots differ')
    capture(attempt / 'check_probe_v2.py', SMALL, FIXED[G06 / 'check_probe_v2.py'])
    need(result['module'] == MODULE and result['label'] == LABEL and result['rc'] == 0 and
         result['source_sha256'] == sha(source) and result['source_unchanged'] is True and
         result['fresh_nonempty_object'] is True and result['error_diagnostics'] == 0 and not ERROR.search(log),
         'native attempt is not a completed fresh error-free C3 run')
    need(re.findall(r'(?m)^START (\S+)\s*$', log) == [result['start']] and
         re.findall(r'(?m)^SOURCE_SHA256 ([0-9a-f]{64})\s*$', log) == [sha(source)] and
         re.findall(r'(?m)^END (\S+) RC (-?\d+)\s*$', log) == [(result['end'], '0')] and
         log.rstrip().endswith('RC 0'), 'native START/END/source markers differ')
    start, end = (dt.datetime.fromisoformat(result[n]) for n in ('start', 'end'))
    prepared = dt.datetime.fromisoformat(m['prepared_utc'])
    need(start.tzinfo is not None and end.tzinfo is not None and prepared <= start <= end,
         'native times precede the reviewed R2 preparation or are invalid')
    setup = read_json(ROOT / 'briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-run/setup-summary.json')
    need(setup['olean_tree'] == m['olean_tree'], 'native tree differs from fixed setup')
    obj = Path(m['olean_tree']) / (MODULE + '.olean')
    need(obj.stat().st_size > 0 and obj.stat().st_mtime >= start.timestamp(), 'missing/stale native C3 object')
    need(isinstance(result['object_sha256'], str) and re.fullmatch('[0-9a-f]{64}', result['object_sha256']),
         'missing/malformed native object SHA')
    capture(obj, TABLE, result['object_sha256'])
    return result, log

def parse(log, modules, expected):
    phase, index, current, remaining = 0, 0, None, 0
    roots, pairs, seen, module_counts, controls = [], [], set(), {}, []
    begin = f'base={BASE} head={HEAD} modules=54'
    for number, raw in enumerate(log.splitlines(), 1):
        need(len(raw) <= MAX_LINE, 'native log line exceeds size bound')
        wrapped = re.fullmatch(r'.+\.lean:\d+:\d+: info: (G06-C3-.*)', raw)
        line = wrapped[1] if wrapped else raw
        if not line.startswith('G06-C3-'):
            continue
        if match := re.fullmatch(r'G06-C3-PRUNING nonTCS_modules=(\d+) direct_edges=(\d+) checked=true', line):
            need(phase == 0 and int(match[1]) > 0, 'duplicate/out-of-order/empty pruning check')
            pruning = {'nonTCS_modules': int(match[1]), 'direct_edges': int(match[2])}; phase = 1
        elif match := re.fullmatch(r'G06-C3-CONTROL generated expected=1 actual=1 reference=(\S+) parent=(\S+) parent_home=(\S+) reference_home=(\S+)', line):
            need(phase == 1 and match[1] == 'BoolCircuit.TreeCircuit.size.eq_def' and
                 match[2] == 'BoolCircuit.TreeCircuit.size', 'invalid generated sensitivity control')
            controls.append({'case': 'generated', 'reference': match[1], 'parent': match[2],
                 'parent_home': match[3], 'reference_home': match[4], 'expected': 1, 'actual': 1}); phase = 2
        elif line == 'G06-C3-CONTROL published_reader expected=0 actual=0 reference=BoolCircuit.TreeCircuit.size_node':
            need(phase == 2, 'duplicate/out-of-order reader sensitivity control')
            controls.append({'case': 'published_reader', 'reference': 'BoolCircuit.TreeCircuit.size_node', 'expected': 0, 'actual': 0}); phase = 3
        elif line == 'G06-C3-BEGIN ' + begin:
            need(phase == 3, 'invalid/duplicate census BEGIN'); phase = 4
        elif match := re.fullmatch(r'G06-C3-MODULE-BEGIN (\S+) \| roots=(\d+)', line):
            need(phase == 4 and current is None and index < 54 and match[1] == modules[index] and
                 int(match[2]) == len(expected[match[1]]), 'invalid/incomplete module BEGIN')
            current = {'module': match[1], 'roots': set(), 'pairs': 0}; remaining = 0
        elif line.startswith('G06-C3-ROOT '):
            parts = line[len('G06-C3-ROOT '):].split(' | ')
            need(phase == 4 and current is not None and remaining == 0 and len(parts) == 8, 'incomplete/out-of-order ROOT')
            mod, owner = map(field, parts[:2])
            keys = ['type_refs', 'value_refs', 'visited', 'pruned', 'unknown_home_types', 'hits']
            values = [re.fullmatch(re.escape(k) + r'=(\d+)', item) for k, item in zip(keys, parts[2:])]
            need(all(values) and mod == current['module'] and owner in expected[mod] and owner not in current['roots'], 'duplicate/unknown/malformed ROOT identity')
            row = {'module': mod, 'owner': owner, **{k: int(v[1]) for k, v in zip(keys, values)}, 'log_line': number}
            need(row['hits'] <= row['visited'] and row['pruned'] + row['unknown_home_types'] <= row['visited'], 'inconsistent ROOT metrics')
            current['roots'].add(owner); current['owner'] = owner; remaining = row['hits']; roots.append(row)
        elif line.startswith('G06-C3-REF '):
            parts = line[len('G06-C3-REF '):].split(' | ')
            need(phase == 4 and current is not None and remaining > 0 and len(parts) == 6, 'unexpected/extra REF')
            mod, owner, ref, parent, parent_home, ref_home = map(field, parts)
            key = (mod, owner, ref)
            need(mod == current['module'] and owner == current['owner'] and key not in seen and
                 re.fullmatch(r'.*\.(?:eq_\d+|eq_def|eq_unfold)', ref) and parent_home != mod and
                 (parent_home == 'TCSlib' or parent_home.startswith('TCSlib.')), 'invalid/duplicate foreign equation REF')
            seen.add(key); pairs.append({'module': mod, 'owner': owner, 'reference': ref, 'parent': parent,
                 'parent_home': parent_home, 'reference_home': ref_home, 'log_line': number})
            need(len(pairs) <= MAX_PAIRS, 'REF count exceeds explicit extraction bound')
            remaining -= 1; current['pairs'] += 1
        elif match := re.fullmatch(r'G06-C3-MODULE-END (\S+) \| roots=(\d+) \| pairs=(\d+)', line):
            need(phase == 4 and current is not None and remaining == 0 and match[1] == current['module'] and
                 current['roots'] == expected[match[1]] and int(match[2]) == len(current['roots']) and
                 int(match[3]) == current['pairs'], 'incomplete/inconsistent module END or exact identity set')
            module_counts[match[1]] = {'roots': int(match[2]), 'pairs': int(match[3])}
            current = None; index += 1
        elif match := re.fullmatch(re.escape('G06-C3-END ' + begin) + r' roots=(\d+) pairs=(\d+) type_extractions=(\d+) value_extractions=(\d+)', line):
            need(phase == 4 and current is None and index == 54 and int(match[1]) == len(roots) == 2881 and
                 int(match[2]) == len(pairs) == sum(x['hits'] for x in roots) and
                 int(match[4]) == len(roots) + 2 and int(match[3]) >= int(match[4]), 'incomplete/inconsistent global END')
            totals = {'roots': int(match[1]), 'pairs': int(match[2]), 'type_extractions': int(match[3]), 'value_extractions': int(match[4])}; phase = 5
        else:
            need(False, 'unknown/malformed C3 marker at log line ' + str(number))
    need(phase == 5 and len(module_counts) == 54 and len(roots) == 2881, 'missing C3 completion or identities')
    return roots, pairs, module_counts, controls, pruning, totals

def kinds_for(roots, pairs, controls):
    validation = read_json(HERE / 'final-explicit-native-table-r1/catalog-validation.json')
    need(validation['status'] == 'NATIVE_KIND_CATALOG_VERIFIED_SCAN_NOT_RUN' and validation['base'] == BASE and
         validation['head'] == HEAD and validation['native_kinds_sha256'] == FIXED[KINDS], 'kind-table validation differs')
    wanted = ({x['owner'] for x in roots} | {x[k] for x in pairs for k in ('reference', 'parent')} |
        {'BoolCircuit.TreeCircuit.size', 'BoolCircuit.TreeCircuit.size.eq_def', 'BoolCircuit.TreeCircuit.size_node'})
    found, count = {}, 0
    with KINDS.open(encoding='utf-8') as handle:
        for line in handle:
            need(len(line) <= MAX_LINE, 'kind-table line exceeds bound')
            fields = line.rstrip('\n').split('\t'); need(len(fields) == 3, 'malformed native kind row'); count += 1
            name, kind, home = fields
            if name in wanted:
                need(name not in found, 'duplicate actual Name in native kind table'); found[name] = (kind, home)
    need(count == validation['rows'] == 378176, 'incomplete native kind table')
    basic = 'TCSlib.Complexity.CircuitComplexity.Basic'
    need(found.get('BoolCircuit.TreeCircuit.size', ('', ''))[0] in DEF_KINDS and
         found.get('BoolCircuit.TreeCircuit.size', ('', ''))[1] == basic and
         found.get('BoolCircuit.TreeCircuit.size.eq_def') == found.get('BoolCircuit.TreeCircuit.size_node') == ('thm', basic) and
         controls[0]['parent_home'] == controls[0]['reference_home'] == basic, 'sensitivity controls disagree with native kinds')
    unresolved = []
    for row in roots:
        item = found.get(row['owner'])
        if item is None:
            unresolved.append({'role': 'owned_root', 'module': row['module'], 'name': row['owner']})
        else:
            need(item[1] == row['module'], 'owned root home disagrees with native kind table')
    for row in pairs:
        for role, name, home in [('reference', row['reference'], row['reference_home']), ('parent', row['parent'], row['parent_home'])]:
            item = found.get(name)
            if item is None:
                unresolved.append({'role': role, 'module': row['module'], 'owner': row['owner'], 'name': name})
            else:
                need(item[1] == home and (item[0] == 'thm' if role == 'reference' else item[0] in DEF_KINDS),
                     'REF kind/home disagrees with native kind table: ' + name)
        row['reference_native_kind'] = found.get(row['reference'], (None, None))[0]
        row['parent_native_kind'] = found.get(row['parent'], (None, None))[0]
    return unresolved

def encoded(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('attempt', type=Path); parser.add_argument('output', type=Path)
    args = parser.parse_args()
    need(not args.output.exists() and not args.output.is_symlink(), 'output already exists')
    attempt, output = args.attempt.resolve(), args.output.resolve()
    need(output.is_relative_to(G06.resolve()) and not output.exists() and output.parent.is_dir() and
         not output.is_relative_to(attempt), 'output must be fresh ignored scratch outside the native attempt')
    m, modules, expected, source = context()
    result, log = native(attempt, m, source)
    roots, pairs, module_counts, controls, pruning, totals = parse(log, modules, expected)
    unresolved = kinds_for(roots, pairs, controls)
    summary = {'status': 'EXTRACTED_METADATA_UNRESOLVED_REVIEW_REQUIRED' if unresolved else 'C3_CENSUS_EXTRACTED_NO_CLEARANCE',
        'base': BASE, 'head': HEAD, 'modules': 54, 'actual_identities': 2881, 'exact_identity_sets_match': True,
        'equation_pairs': len(pairs), 'module_counts': module_counts, 'controls': controls, 'pruning': pruning,
        'totals': totals, 'unresolved_kind_metadata': unresolved, 'rule10_clearance': False,
        'source_failure_exclusions': False, 'notation_filtering': False,
        'limit': 'Collection/extraction only. Every pair is retained; all findings and unknown metadata require root review.'}
    payloads = {'summary.json': encoded(summary), 'all-refs.json': encoded(pairs), 'root-census.json': encoded(roots)}
    for mod in modules:
        payloads['eqn/' + mod + '.eqn.txt'] = ''.join('\t'.join([x['module'], x['owner'], x['parent'], x['reference']]) + '\n'
             for x in pairs if x['module'] == mod).encode()
    check_head()
    for path, record in list(INPUTS.items()):
        capture(Path(path), record['cap'], record['sha256'])
    need(not output.exists(), 'output appeared during validation')
    raw_manifest = {'base': BASE, 'head': HEAD, 'attempt': str(attempt), 'output': str(output),
        'extractor_sha256': INPUTS[str(Path(__file__).resolve())]['sha256'], 'inputs': INPUTS,
        'native_result': result, 'canonical_axioms_sha256': FIXED[E / 'axioms-full.json'],
        'scanner_directory': str(output / 'eqn'), 'scanner_row_fields': ['module', 'owner', 'parent', 'eqnref'],
        'all_54_files_required_including_zero_byte_files': True, 'output_sha256': {n: sha(b) for n, b in payloads.items()},
        'exit_status': 1 if unresolved else 0, 'rule10_clearance': False, 'source_failure_exclusions': False}
    payloads['manifest.json'] = encoded(raw_manifest)
    output.mkdir(); (output / 'eqn').mkdir()
    # Completion metadata is last; an interrupted write cannot masquerade as a full artifact set.
    order = [n for n in payloads if n not in {'summary.json', 'manifest.json'}] + ['summary.json', 'manifest.json']
    for name in order:
        raw = payloads[name]
        with (output / name).open('xb') as handle:
            handle.write(raw)
    print(json.dumps({'status': summary['status'], 'pairs': len(pairs), 'unresolved_metadata': len(unresolved),
        'summary_sha256': sha(payloads['summary.json']), 'manifest_sha256': sha(payloads['manifest.json']), 'output': str(output)}))
    return 1 if unresolved else 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as error:
        print('C3-EXTRACT-FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
