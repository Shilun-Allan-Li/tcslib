"""Source-only cache qualification census/request/source-regeneration audit.
Never executes Lean, imported generator module top-level code, or writes active paths.
"""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).parent
EVIDENCE = HERE.parent.parent
QUAL = EVIDENCE / 'logs/seals/cache-qualification-r1'
PROPOSAL = EVIDENCE / 'proposals/cached-module-names-r3'
NATIVE = EVIDENCE / 'logs/seals/finalr2planted-native-r1'
REVISION = '47ced271090f45918645c842cd358c5079092754'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
load = lambda path: json.loads(path.read_text())

candidate_raw = (PROPOSAL / 'prepare_seals_candidate.py').read_bytes()
original_raw = (PROPOSAL / 'prepare_seals.original.py').read_bytes()
metadata = load(PROPOSAL / 'metadata.json')
# Execute only these inspected pure function definitions; no argparse/top-level code.
tree = ast.parse(candidate_raw.decode())
allowed_functions = {'lean_string', 'blank_comments', 'imports', 'parse_catalog', 'seal_command', 'instrument'}
nodes = [node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name in allowed_functions]
assert {node.name for node in nodes} == allowed_functions
namespace = {'json': json, 're': re}
exec(compile(ast.Module(body=nodes, type_ignores=[]), str(PROPOSAL / 'prepare_seals_candidate.py') + ':pure-functions-only', 'exec'), namespace)
make_seals = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == 'make_seals')
control_block = next(node for node in make_seals.body if isinstance(node, ast.If) and isinstance(node.test, ast.Name) and node.test.id == 'ordinary')
control_literals = {}
for node in control_block.body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
        if node.targets[0].id in {'negative', 'positive', 'sensitivity_symbol'}:
            control_literals[node.targets[0].id] = ast.literal_eval(node.value)
assert set(control_literals) == {'negative', 'positive', 'sensitivity_symbol'}
assert control_literals['sensitivity_symbol'] == 'Complexity.NUPPT.inArg'

# Verify the entire proposal is only the pure cache change.
needle = '  let env ← Lean.getEnv\n  let mut catalog : Std.HashMap String (Array Lean.Name) := {{}}\n'
expected_candidate = original_raw.decode()
assert expected_candidate.count(needle) == 1
expected_candidate = expected_candidate.replace(needle, '  let env ← Lean.getEnv\n  let moduleNames := env.header.moduleNames\n  let mut catalog : Std.HashMap String (Array Lean.Name) := {{}}\n')
start = expected_candidate.index('def seal_command(')
end = expected_candidate.index('\ndef ', start + 1)
part = expected_candidate[start:end]
assert part.count('env.header.moduleNames[mi.toNat]!') == 2
expected_candidate = expected_candidate[:start] + part.replace('env.header.moduleNames[mi.toNat]!', 'moduleNames[mi.toNat]!') + expected_candidate[end:]
assert candidate_raw == expected_candidate.encode()

manifest_raw = (QUAL / 'seal-manifest.json').read_bytes()
manifest = json.loads(manifest_raw)
prep = load(QUAL / 'preparation-manifest.json')
record = prep['records'][0]
original_prep = load(EVIDENCE / 'seals/FinalR2Planted/manifest.json')
peer = load(EVIDENCE / 'audits/final18-peer-census-r1/batch003.json')
previous = next(row for row in peer['phases'] if row['phase'] == 'FinalR2Planted')
collector = EVIDENCE / previous['collector_log']
catalog, ends = namespace['parse_catalog'](collector)
rows = catalog[record['target']]
keys = [(row['spelling'], row['home']) for row in rows]
foreign = [row for row in rows if row['home'] != record['snapshot_module']]
eligible = [row for row in foreign if row['is_definition'] and not row['instance'] and row['status'] != 'reducible']
eligible.sort(key=lambda row: row['spelling'])
source = (EVIDENCE / 'seals/CacheBenchPlanted' / record['raw_source']).read_bytes()
raw_retained = [(QUAL / 'sources' / (r['label'] + '.original.lean')).read_bytes() for r in manifest['probes'] if not r.get('control')]
old_seals = load(EVIDENCE / 'seals/FinalR2Planted/seal-manifest.json')
all_checks = {
    'fixed_revision': record['revision'] == REVISION,
    'proposal_hashes_match_metadata': sha(candidate_raw) == metadata['candidate_sha256'] and sha(original_raw) == metadata['original_sha256'],
    'proposal_original_exact_versioned_origin': Path(metadata['origin']).read_bytes() == original_raw,
    'proposal_only_pure_cache_changes': candidate_raw == expected_candidate.encode(),
    'preparation_records_exact_original_frozen_records': prep['records'] == original_prep['records'],
    'collector_is_previously_independently_audited': previous['native_census'] == previous['request_coverage'] == 'PASS',
    'collector_hash_matches_manifest_and_previous': sha(collector.read_bytes()) == manifest['inventory_log_sha256'] == previous['collector_log_sha256'],
    'exact_closure_marker100': collector.read_text().splitlines().count('LAMP-CLOSURE-EXACT\t' + record['target'] + '\t100') == 1 and len(record['closure']) == 100,
    'catalog_unique_actual_spelling_home_pairs': len(keys) == len(set(keys)),
    'catalog_homes_within_exact_closure_or_own': all(row['home'] in record['closure'] or row['home'] == record['snapshot_module'] for row in rows),
    'catalog_end_complete': ends[record['target']] == (len(rows), 67, 100),
    'retained_target_source_hash_matches_record': sha(source) == record['source_sha256'],
    'both_retained_originals_are_frozen_target': len(raw_retained) == 2 and all(raw == source for raw in raw_retained),
    'qualification_manifest_matches_runner_bound_hash': sha(manifest_raw) == load(QUAL / 'metadata.json')['manifest_sha256'],
    'exact_two_source_and_six_control_probes': len(manifest['probes']) == 8 and sum(bool(r.get('control')) for r in manifest['probes']) == 6,
}
reviews = []
for probe in manifest['probes']:
    label = probe['label']
    actual = (QUAL / 'sources' / (label + '.lean')).read_bytes()
    control = bool(probe.get('control'))
    mode = probe['mode'] if not control else re.fullmatch(r'CacheBenchPlanted_Control([AB])(Unsealed|Negative|Reader)', label).group(1)
    selected = [row for row in eligible if mode == 'B' or row['spelling'] != 'Complexity.PolyExpr.eval']
    expected_requests = [] if control and label.endswith('Unsealed') else selected
    if not control:
        regenerated, mapping = namespace['instrument'](source, label, selected)
        extra = {'line_map_matches_candidate_instrument': mapping == probe['original_line_map'],
                 'target_source_bound': probe['target'] == record['target'] and probe['source_sha256'] == record['source_sha256']}
    else:
        kind = re.fullmatch(r'CacheBenchPlanted_Control[AB](Unsealed|Negative|Reader)', label).group(1)
        header = 'import Lean\n' + ''.join('import ' + name + '\n' for name in namespace['imports'](source))
        regenerated = header + '\nset_option maxHeartbeats 0\n'
        if kind != 'Unsealed': regenerated += namespace['seal_command'](label, selected)
        proof_line = len(regenerated.splitlines()) + 2
        regenerated += control_literals['positive' if kind == 'Reader' else 'negative']
        if kind != 'Unsealed': regenerated += namespace['seal_command'](label, selected, verify=True)
        extra = {'control_sensitivity_symbol_from_candidate': probe['sensitivity_symbol'] == control_literals['sensitivity_symbol'],
                 'expected_error_count_from_candidate': probe['expected_errors'] == int(kind == 'Negative'),
                 'expected_error_line_from_candidate': probe['expected_error_line'] == (proof_line if kind == 'Negative' else None)}
    old_label = label.replace('CacheBenchPlanted', 'FinalR2Planted')
    old_probe = next(row for row in old_seals['probes'] if row['label'] == old_label)
    old_source = (NATIVE / 'sources' / (old_label + '.lean')).read_text().replace(old_label, label)
    expected_pure_cache = old_source.replace('  let env ← Lean.getEnv\n', '  let env ← Lean.getEnv\n  let moduleNames := env.header.moduleNames\n').replace('env.header.moduleNames[mi.toNat]!', 'moduleNames[mi.toNat]!')
    result = load(QUAL / (label + '.result.json'))
    tests = {
        'exact_request_rows_from_complete_catalog': probe['requests'] == expected_requests,
        'request_pairs_unique': len(probe['requests']) == len({(r['spelling'], r['home']) for r in probe['requests']}),
        'requests_exact_original_native_requests': probe['requests'] == old_probe['requests'],
        'probe_hash_matches_manifest_and_result': sha(actual) == probe['probe_sha256'] == result['source_sha256'],
        'actual_source_exact_candidate_pure_regeneration': actual == regenerated.encode(),
        'actual_source_only_original_plus_cache_and_label': actual == expected_pure_cache.encode(),
        'retained_result_log_hash_bound': sha((EVIDENCE / result['raw_log']).read_bytes()) == result['raw_log_sha256'],
        **extra,
    }
    reviews.append(dict(label=label, mode=mode, control=control, request_count=len(probe['requests']), source_sha256=sha(actual), regenerated_sha256=sha(regenerated.encode()), tests=tests, passed=all(tests.values())))

# The runner retained a generic snapshot of its active old tool. Preserve that fact;
# supplemental provenance is established by exact regeneration above, not relabeling it.
retained_tool_hash = sha((QUAL / 'prepare_seals.py').read_bytes())
summary = {
    'scope': 'Independent source-only qualification catalog/request/hash and exact pure-function regeneration audit. Raw seal/control marker interpretation is separately audited by route_audit. No Lean executed.',
    'revision': REVISION,
    'all_pass': all(all_checks.values()) and all(row['passed'] for row in reviews),
    'checks': all_checks,
    'inventory_log': str(collector.relative_to(EVIDENCE)),
    'inventory_log_sha256': sha(collector.read_bytes()),
    'qualification_manifest_sha256': sha(manifest_raw),
    'candidate_generator': str((PROPOSAL / 'prepare_seals_candidate.py').relative_to(EVIDENCE)),
    'candidate_generator_sha256': sha(candidate_raw),
    'retained_generic_prepare_tool_sha256': retained_tool_hash,
    'retained_generic_prepare_tool_is_candidate': retained_tool_hash == sha(candidate_raw),
    'provenance_qualification': 'The generic runner prepare_seals.py snapshot is the old active tool, not the candidate. This supplemental audit exactly regenerates all eight actual retained probe bytes from the correctly hashed candidate pure functions and fixed original/control bodies, thereby binding candidate semantics without falsely relabeling that retained snapshot.',
    'closure_modules': len(record['closure']),
    'own_stored_constants': previous['own_stored_constants'],
    'own_axiom_sets': previous['own_axiom_set_counts'],
    'catalog_rows': len(rows), 'foreign_constants': len(foreign), 'eligible_definitions_B': len(eligible),
    'eligible_private_names': sum(row['spelling'].startswith('_private.') for row in eligible),
    'eligible_matchers': sum(row['matcher'] for row in eligible),
    'eligible_home_count': len({row['home'] for row in eligible}),
    'eligible_homes': sorted(Counter(row['home'] for row in eligible).items()),
    'probes': reviews, 'audit_tool_sha256': sha(Path(__file__).read_bytes()),
}
output = HERE / 'review.json'
assert not output.exists()
output.write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({key: summary[key] for key in ['all_pass','closure_modules','own_stored_constants','eligible_definitions_B','eligible_private_names','eligible_matchers','eligible_home_count','retained_generic_prepare_tool_is_candidate']}, indent=2))
for row in reviews: print(row['label'], row['passed'], row['request_count'])
