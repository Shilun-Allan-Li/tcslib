"""Independent source-only cached collector qualification comparison; no Lean."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
HERE = Path(__file__).parent
EVIDENCE = HERE.parent.parent
PROPOSAL = EVIDENCE / 'proposals/cached-collector-planted-r1'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
load = lambda path: json.loads(path.read_text())
metadata = load(PROPOSAL / 'metadata.json')
original = (PROPOSAL / 'Inventory.original.lean').read_bytes()
cached = (PROPOSAL / 'Inventory.cached.lean').read_bytes()
original_log_path = EVIDENCE / 'logs/helper-checks/Inventory-FinalR2PlantedInventory01.log'
new_log_path = EVIDENCE / 'logs/helper-checks/PlantedInventoryCached-Cache01.log'
original_log = original_log_path.read_bytes()
new_log = new_log_path.read_bytes()
source_capture = EVIDENCE / 'logs/helper-checks/PlantedInventoryCached-Cache01.source.lean'
expected = original.decode()
assert expected.count('env.header.moduleNames') == 4
assert expected.count('  let env ← getEnv\n') == 1
expected = expected.replace('env.header.moduleNames', 'moduleNames').replace('  let env ← getEnv\n', '  let env ← getEnv\n  let moduleNames := env.header.moduleNames\n')
marker_prefixes = ('LAMP-CATALOG\t', 'LAMP-AXIOMS\t', 'LAMP-CLOSURE-EXACT\t', 'LAMP-INVENTORY-END\t')
def marker_rows(raw):
    return [line for line in raw.decode().splitlines() if line.startswith(marker_prefixes)]
old_markers, new_markers = marker_rows(original_log), marker_rows(new_log)
old_counts = Counter(line.split('\t')[0] for line in old_markers)
new_counts = Counter(line.split('\t')[0] for line in new_markers)
helper_rows = [json.loads(line) for line in (EVIDENCE / 'logs/helper-checks/results.jsonl').read_text().splitlines()]
result = [row for row in helper_rows if row.get('module') == 'LamportEvidence/CacheQualification/PlantedInventoryCached' and row.get('attempt') == 'Cache01']
assert len(result) == 1
result = result[0]
expected_counts = {'LAMP-CATALOG': 9103, 'LAMP-AXIOMS': 67, 'LAMP-CLOSURE-EXACT': 1, 'LAMP-INVENTORY-END': 1}
previous = load(EVIDENCE / 'audits/final18-peer-census-r1/batch003.json')
prior = next(row for row in previous['phases'] if row['phase'] == 'FinalR2Planted')
checks = {
    'fixed_revision': metadata['source_commit'] == '47ced271090f45918645c842cd358c5079092754',
    'original_hash_matches_metadata': sha(original) == metadata['original_source_sha256'],
    'cached_hash_matches_metadata': sha(cached) == metadata['cached_source_sha256'],
    'original_exact_retained_qualified_source': original == Path(metadata['qualified_old_native_source']).read_bytes(),
    'original_exact_hardened_proposal_origin': original == Path(metadata['origin']).read_bytes(),
    'candidate_is_exact_one_binding_four_read_substitutions': cached == expected.encode(),
    'actual_native_source_exact_cached_candidate': source_capture.read_bytes() == cached,
    'source_imports_same_snapshot_only': re.findall(r'^import (.+)$', cached.decode(), re.M) == ['Lean', 'LamportEvidence.Seals.FinalR2Planted.Snapshot0'],
    'native_result_expected_module_log_status_hash': result['exit'] == 0 and result['source_sha256'] == sha(cached) and result['log'] == str(new_log_path.relative_to(EVIDENCE)),
    'native_raw_log_source_hash_bound': ('source-sha256=' + sha(cached)) in new_log.decode(),
    'old_and_new_terminal_success': original_log.decode().rstrip().endswith('exit=0') and new_log.decode().rstrip().endswith('exit=0'),
    'old_and_new_no_Lean_error': not any(re.search(r'\.lean:\d+:\d+: error:', raw.decode()) for raw in (original_log,new_log)),
    'old_hash_bound_previous_independent_census': sha(original_log) == prior['collector_log_sha256'] and prior['native_census'] == prior['request_coverage'] == 'PASS',
    'all_marker_rows_exact_in_original_order': new_markers == old_markers,
    'marker_counts_complete': dict(old_counts) == dict(new_counts) == expected_counts,
    'exact_closure100_marker': [line for line in new_markers if line.startswith('LAMP-CLOSURE-EXACT\t')] == ['LAMP-CLOSURE-EXACT\tTCSlib.Cryptography.Authentication.Signatures.Lamport.Planted\t100'],
    'inventory_end_exact': [line for line in new_markers if line.startswith('LAMP-INVENTORY-END\t')] == ['LAMP-INVENTORY-END\tTCSlib.Cryptography.Authentication.Signatures.Lamport.Planted\t9103\t67\t100'],
    'strict_extra_home_guard_preserved': all(token in cached.decode() for token in ['for imported in moduleNames do','if (`TCSlib).isPrefixOf imported then','unless homes.contains imported.toString do','unless exactHomes == homes.length do']),
}
base_queue = EVIDENCE / 'preparation/final18-r2/cached-installer-r3-provenance-r1/queue.json'
queue = load(base_queue)
summary = {
    'scope': 'Independent source-only cache collector qualification: full exact marker sequence, source/hash/module scope and original hardening preservation. No Lean or active changes. No claim for future phase collectors.',
    'all_pass': all(checks.values()), 'checks': checks,
    'original_source_sha256': sha(original), 'cached_source_sha256': sha(cached),
    'original_log_sha256': sha(original_log), 'new_log_sha256': sha(new_log),
    'old_marker_counts': dict(old_counts), 'new_marker_counts': dict(new_counts),
    'new_module': result['module'], 'new_log': str(new_log_path.relative_to(EVIDENCE)),
    'new_runtime_check': result,
    'old_own_axiom_sets_preserved': prior['own_axiom_set_counts'],
    'new_base_queue': str(base_queue.relative_to(EVIDENCE)), 'new_base_queue_sha256': sha(base_queue.read_bytes()),
    'new_base_queue_qualification': 'Located installer provenance-r1 queue; future cached collector overlay is not yet claimed reviewed here. First four phases remain adopted old native results. Legacy top-level prepare_tool_sha256/origin still describe original preparation; current cached generator binding is installer_r3.tool_versions and actual_generator supplementary provenance.',
    'new_base_queue_current_prepare_tool_sha256': sha(Path(queue['prepare_tool']).read_bytes()),
    'new_base_queue_legacy_prepare_tool_sha256': queue['prepare_tool_sha256'],
    'audit_tool_sha256': sha(Path(__file__).read_bytes()),
}
output = HERE / 'collector-review.json'
assert not output.exists()
output.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({key: summary[key] for key in ['all_pass','cached_source_sha256','new_log_sha256','new_marker_counts','new_module']},indent=2))
