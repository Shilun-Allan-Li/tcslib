"""Source-only cache-overlay and first-four native adoption provenance audit.
No Lean or generator top-level execution; writes only its fresh audit JSON.
"""
import ast
import hashlib
import json
from pathlib import Path
import re
HERE = Path(__file__).parent
EVIDENCE = HERE.parent.parent
QUEUE = EVIDENCE / 'preparation/final18-r2/cached-collectors-r3/queue.json'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
load = lambda path: json.loads(path.read_text())
queue = load(QUEUE)
overlay = queue['collector_cache_overlay']
base_path = Path(overlay['original_queue'])
base_raw = base_path.read_bytes()
base = json.loads(base_raw)
initial_path = Path(queue['adopted_native_queue']['path'])
initial_raw = initial_path.read_bytes()
initial = json.loads(initial_raw)
original = load(EVIDENCE / 'preparation/final18-r2/queue.json')
prior = load(HERE / 'batch003.json')
prior_phases = {row['phase']:row for row in prior['phases']}
static = load(HERE / 'static-source-review.json')
assert static['all_static_checks_pass']
versions = queue['inventory_hardening']['tool_versions']
source_hashes = overlay['source_sha256_before']
frozen_hashes = queue['inventory_hardening']['source_sha256_before']
root = Path(queue['records'][0]['root'])
checks = {
    'fixed_revision_and_all18': queue['revision'] == base['revision'] == initial['revision'] == '47ced271090f45918645c842cd358c5079092754' and len(queue['records']) == len(base['records']) == 18,
    'base_queue_hash_bound': sha(base_raw) == overlay['original_queue_sha256'],
    'adopted_initial_queue_hash_bound': sha(initial_raw) == queue['adopted_native_queue']['sha256'],
    'first4_adopted_exact_named_phases': queue['adopted_native_queue']['phases'] == [row['phase'] for row in queue['records'][:4]] == ['FinalR2Planted','FinalR2Encoding','FinalR2TableCoins','FinalR2Averaging'],
    'first4_records_unchanged_from_precollector_base': queue['records'][:4] == base['records'][:4],
    'all177_TCS_sources_unchanged': len(source_hashes) == 177 and source_hashes == overlay['source_sha256_after'] == frozen_hashes == {module:sha((root/(module+'.lean')).read_bytes()) for module in source_hashes},
    'all_retained_tool_hashes_correct': all(sha(Path(row['snapshot']).read_bytes()) == row['sha256'] for row in versions.values()),
    'cached_generator_hash_exact_qualified_proposal': sha(Path(queue['prepare_tool']).read_bytes()) == '35d744b699ebc16a198eea51336e5ef0b261a487a0df946857be1715e4e0f9db',
    'all14_updates_only': len(overlay['updates']) == 14 and [row['phase'] for row in overlay['updates']] == [row['phase'] for row in queue['records'][4:]],
    'qualification_gate_hashes_correct': all(sha(Path(queue['activation_gate'][key]).read_bytes()) == queue['activation_gate'][key+'_sha256'] for key in ['full_planted_qualification_summary','cached_collector_comparison']),
}
updated = []
for record, previous, original_record in zip(queue['records'][4:],base['records'][4:],original['records'][4:]):
    phase = record['phase']
    folder = Path(record['collector_cached_source']).parent
    old_source = (folder/'Inventory.original.lean').read_bytes()
    hardened = (folder/'Inventory.hardened.lean').read_bytes()
    cached = (folder/'Inventory.cached.lean').read_bytes()
    expected = hardened.decode()
    assert expected.count('env.header.moduleNames') == 4
    assert expected.count('  let env ← getEnv\n') == 1
    expected = expected.replace('env.header.moduleNames','moduleNames').replace('  let env ← getEnv\n','  let env ← getEnv\n  let moduleNames := env.header.moduleNames\n')
    manifest_raw = Path(record['manifest']).read_bytes()
    manifest = json.loads(manifest_raw)
    cm = load(Path(record['collector_cached_manifest']))
    original_manifest = load(folder/'manifest.original.json')
    delta_keys = {key for key in previous if record.get(key) != previous[key]}
    tests = {
        'phase_revision_snapshot_target_closure_unchanged': all(record[key] == previous[key] for key in ['phase','revision','target','snapshot_module','source_sha256','closure_modules','manifest','manifest_sha256','collector_module']),
        'old_record_only_two_existing_fields_changed': delta_keys == {'collector_source_sha256','collector_tool_version'},
        'original_hardened_cached_hash_bindings': sha(old_source) == record['collector_original_source_sha256'] == original_record['collector_source_sha256'] and sha(hardened) == record['collector_hardened_source_sha256'] == previous['collector_source_sha256'] and sha(cached) == record['collector_source_sha256'],
        'hardened_exact_previous_retained_source': hardened == Path(previous['collector_hardened_source']).read_bytes(),
        'only_pure_cache_delta': cached == expected.encode(),
        'live_probe_exact_cached_source': (root/(record['collector_module']+'.lean')).read_bytes() == cached,
        'snapshot_imports_same': re.findall(r'^import (.+)$',cached.decode(),re.M) == re.findall(r'^import (.+)$',hardened.decode(),re.M) == ['Lean',record['snapshot_module'].replace('/','.')],
        'strict_closure_guard_preserved': all(token in cached.decode() for token in ['for imported in moduleNames do','if (`TCSlib).isPrefixOf imported then','unless homes.contains imported.toString do','unless exactHomes == homes.length do','LAMP-CLOSURE-EXACT']),
        'original_manifest_unchanged_hash': sha(manifest_raw) == record['manifest_sha256'] and manifest == original_manifest,
        'cached_manifest_only_hash_overlay_added': {k:v for k,v in cm.items() if k not in ['inventory_sha256','native_collector_overlay']} == {k:v for k,v in manifest.items() if k!='inventory_sha256'} and cm['inventory_sha256'] == sha(cached),
    }
    updated.append(dict(phase=phase,tests=tests,passed=all(tests.values()),cached_source_sha256=sha(cached),runtime='NOT_CLAIMED_BY_STATIC_OVERLAY_REVIEW'))

# Load only pure original-generator definitions to check old actual-generator provenance.
generator_path = Path(queue['adopted_native_queue']['original_tool_versions']['prepare_seals_final_r2.py']['snapshot'])
generator_raw = generator_path.read_bytes()
tree = ast.parse(generator_raw.decode())
allowed = {'lean_string','blank_comments','imports','parse_catalog','seal_command','instrument'}
namespace = {'json':json,'re':re}
nodes = [node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name in allowed]
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(generator_path)+':pure-functions-only','exec'),namespace)
make = next(node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name=='make_seals')
control_block = next(node for node in make.body if isinstance(node,ast.If) and isinstance(node.test,ast.Name) and node.test.id=='ordinary')
def literals(block):
    out={}
    for node in block:
        if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in {'negative','positive','sensitivity_symbol'}:
            out[node.targets[0].id]=ast.literal_eval(node.value)
    return out
ordinary_literals=literals(control_block.body)
fallback=next(node for node in control_block.body if isinstance(node,ast.If))
fallback_literals=literals(fallback.body)
first_four=[]
for record in queue['records'][:4]:
    phase=record['phase']
    folder=Path(record['adopted_native_seal_attempt'])
    manifest_raw=(folder/'seal-manifest.json').read_bytes()
    manifest=json.loads(manifest_raw)
    provenance=load(folder/'actual-generator-provenance.json')
    actual_tool=(folder/provenance['actual_generator_copy']).read_bytes()
    summary_folder=EVIDENCE/'logs/final18-native-r3'/phase
    summary=load(summary_folder/'summary.json')
    census=load(summary_folder/'census.json')
    prior_row=prior_phases[phase]
    raw_path=EVIDENCE/prior_row['collector_log']
    catalog,_=namespace['parse_catalog'](raw_path)
    prep=load(Path(record['manifest']))['records'][0]
    eligible=sorted([r for r in catalog[record['target']] if r['home']!=prep['snapshot_module'] and r['is_definition'] and not r['instance'] and r['status']!='reducible'],key=lambda r:r['spelling'])
    source=(Path(record['phase_directory'])/prep['raw_source']).read_bytes()
    literal=ordinary_literals if any(r['spelling']=='Complexity.NUPPT.inArg' for r in catalog[record['target']]) else fallback_literals
    regenerated=[]
    for probe in manifest['probes']:
        label=probe['label'];control=bool(probe.get('control'))
        mode=probe['mode'] if not control else re.fullmatch(phase+r'_Control([AB])(Unsealed|Negative|Reader)',label).group(1)
        selected=[r for r in eligible if mode=='B' or r['spelling']!='Complexity.PolyExpr.eval']
        if not control:
            text,mapping=namespace['instrument'](source,label,selected)
            check_map=mapping==probe['original_line_map']
        else:
            kind=re.fullmatch(phase+r'_Control[AB](Unsealed|Negative|Reader)',label).group(1)
            text='import Lean\n'+''.join('import '+name+'\n' for name in namespace['imports'](source))+'\nset_option maxHeartbeats 0\n'
            if kind!='Unsealed':text+=namespace['seal_command'](label,selected)
            text+=literal['positive' if kind=='Reader' else 'negative']
            if kind!='Unsealed':text+=namespace['seal_command'](label,selected,verify=True)
            check_map=True
        request_rows=[] if control and label.endswith('Unsealed') else selected
        actual=(folder/'sources'/(label+'.lean')).read_bytes()
        regenerated.append(actual==text.encode() and sha(actual)==probe['probe_sha256'] and probe['requests']==request_rows and check_map)
    raw_axioms={}
    for line in raw_path.read_text().splitlines():
        if line.startswith('LAMP-AXIOMS\t'):
            _,target,name,values=line.split('\t',3)
            raw_axioms[name]=[part.strip() for part in values.strip('[]').split(',') if part.strip()]
    tests={
        'previous_census_request_PASS':prior_row['native_census']==prior_row['request_coverage']=='PASS',
        'summary_explicit_old_adoption':summary['native_results_adopted'] is True and summary['adopted_native_queue']==queue['adopted_native_queue'],
        'summary_source_collector_bound_old_checks':summary['revision']==queue['revision'] and summary['target']==record['target'] and summary['collector_attempts'][-1]['raw_log_sha256']==prior_row['collector_log_sha256'],
        'same_full177_phase_before_after':load(summary_folder/'source-hashes-before.json')==load(summary_folder/'source-hashes-after.json')==source_hashes,
        'official_census_exact_raw_own_axioms':{r['constant']:r['axioms'] for r in census['records']}==raw_axioms and census['count']==prior_row['own_stored_constants'],
        'official_census_rawhash_bound':census['raw_log_sha256']==sha(raw_path.read_bytes())==prior_row['collector_log_sha256'],
        'actual_generator_annotated_original_tool_hash':sha(actual_tool)==sha(generator_raw)==provenance['actual_generator_sha256']=='e52171a25f0e51d3ad8743ea8b91d885504d02465310160de24c2c22dc30e3fd',
        'actual_generator_correct_original_path':provenance['actual_generator_path']==str(generator_path),
        'annotation_manifest_hash_bound':provenance['native_attempt_manifest_sha256']==sha(manifest_raw),
        'all8_sources_exact_original_generator_regeneration':len(regenerated)==8 and all(regenerated),
    }
    first_four.append(dict(phase=phase,tests=tests,passed=all(tests.values()),probes_regenerated=len(regenerated),own_constants=census['count'],exact_closure=census['exact_closure'],native_census='PREVIOUS_PASS_ADOPTED_NOT_REEXECUTED'))

payload=dict(scope='Source-only all14 cached collector overlay plus exact first4 old native adoption/provenance review. Future runtime phases are not claimed complete; scan/control outcomes separately audited.',all_pass=all(checks.values()) and all(r['passed'] for r in updated+first_four),checks=checks,queue_sha256=sha(QUEUE.read_bytes()),queue=str(QUEUE.relative_to(EVIDENCE)),updated_collectors=updated,adopted_first_four=first_four,tool_sha256=sha(Path(__file__).read_bytes()),legacy_top_level_prepare_hash_qualification='Top-level prepare_tool_sha256/origin remain original preparation metadata; current generator hashes use retained tool_versions and explicit actual-generator-provenance.json.')
output=HERE/'cached-overlay-review.json'
assert not output.exists()
output.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps(dict(all_pass=payload['all_pass'],updated_collectors_pass=sum(r['passed'] for r in updated),first_four_adoptions_pass=sum(r['passed'] for r in first_four)),indent=2))
for row in updated+first_four:
    if not row['passed']:print(row['phase'],{k:v for k,v in row['tests'].items() if not v})
