"""Summarize complete native final18 evidence, retaining explicit strict-B failures."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

evidence=Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
root=Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
folder=evidence/'logs/final18-native-r3'
queue_path=evidence/'preparation/final18-r2/cached-collectors-r3/queue.json'
queue=json.loads(queue_path.read_text())
overall=json.loads((folder/'summary.json').read_text())
assert overall['status']=='NATIVE_QUEUE_COMPLETE' and overall['count']==18
assert [x['phase'] for x in overall['phases']]==[x['phase'] for x in queue['records']]
sha=lambda raw:hashlib.sha256(raw).hexdigest()
sources=[]
controls=[]
phases=[]
failures=[]
own_count=0
axioms=set()
for record in queue['records']:
    phase=record['phase']
    directory=folder/phase
    summary=json.loads((directory/'summary.json').read_text())
    census=json.loads((directory/'census.json').read_text())
    selection=json.loads((directory/'seal-selection.json').read_text())
    assert summary['source_hashes_unchanged'] and census['status']=='ALL_STORED_CONSTANT_AXIOMS_STANDARD_SUBSET'
    assert census['exact_closure']==record['closure_modules']
    own_count+=census['count']
    for item in census['records']:
        axioms.update(item['axioms'])
    assert sha(Path(census['raw_log']).read_bytes())==census['raw_log_sha256']
    for attempt in selection['attempts']:
        provenance=json.loads((Path(attempt)/'actual-generator-provenance.json').read_text())
        assert sha((Path(attempt)/'actual_prepare_seals.py').read_bytes())==provenance['actual_generator_sha256']
        assert sha((Path(attempt)/'seal-manifest.json').read_bytes())==provenance['native_attempt_manifest_sha256']
    manifest=json.loads((Path(record['phase_directory'])/'seal-manifest.json').read_text())
    manifest_by_label={x['label']:x for x in manifest['probes']}
    assert set(manifest_by_label)=={x['label'] for x in selection['records']}
    phase_sources=[]
    phase_controls=[]
    for item in selection['records']:
        probe=manifest_by_label[item['label']]
        assert item['harness']['valid']
        raw=evidence/item['raw_log']
        assert sha(raw.read_bytes())==item['raw_log_sha256']
        if probe.get('control'):
            assert item['status']=='CONTROL_PASS'
            assert item['errors']==probe['expected_errors']
            assert item['exit']==probe['expected_errors']
            controls.append(item)
            phase_controls.append(item)
        else:
            assert item['source_sha256']==probe['probe_sha256']
            assert probe['source_sha256']==record['source_sha256']
            assert item['status'] in ('SOURCE_PASS','SOURCE_FAIL')
            if item['mode']=='A':
                assert item['status']=='SOURCE_PASS' and item['errors']==0 and item['exit']==0
            sources.append(item)
            phase_sources.append(item)
            if item['status']=='SOURCE_FAIL':
                diagnostics=[]
                for diagnostic in item['diagnostics']:
                    if diagnostic['severity']!='error':continue
                    assert diagnostic['original_line'] is not None and diagnostic['declaration']
                    diagnostics.append(dict(original_file=diagnostic['original_file'],original_line=diagnostic['original_line'],
                        declaration=diagnostic['declaration'],message=diagnostic['message'],
                        diagnostic_excerpt_before_markers=diagnostic['raw_diagnostic_block'].split('LAMP-SEAL-NAME')[0].strip()))
                failures.append(dict(phase=phase,mode=item['mode'],errors=item['errors'],raw_log=item['raw_log'],
                    raw_result=str(Path(item['selected_attempt'])/(item['label']+'.result.json')),
                    declarations=sorted({d['declaration'] for d in diagnostics}),diagnostics=diagnostics))
    assert len(phase_sources)==2 and {x['mode'] for x in phase_sources}=={'A','B'}
    assert len(phase_controls)==(0 if record['closure_modules']==0 else 6)
    phases.append(dict(phase=phase,target=record['target'],exact_tcs_closure=record['closure_modules'],stored_own_constants=census['count'],
        A=next(x['status'] for x in phase_sources if x['mode']=='A'),B=next(x['status'] for x in phase_sources if x['mode']=='B'),
        control_count=len(phase_controls),source_sha256=record['source_sha256'],
        collector_log=census['raw_log'],scan=str(directory/'explicit-unfold-scan.json')))
assert len(sources)==36 and len(controls)==102
assert sum(x['expected_errors']==1 for x in controls)==34
assert axioms<= {'propext','Classical.choice','Quot.sound'}
audit=json.loads((evidence/'inputs/final-r2-order-audit.json').read_text())
assert {m:sha((root/(m+'.lean')).read_bytes()) for m in audit['source_sha256']}==audit['source_sha256']
assert subprocess.check_output(['git','--no-optional-locks','-C',str(root),'rev-parse','HEAD'],text=True).strip()==queue['revision']
result=dict(status='NATIVE_COMPLETE_ALL_A_PASS_STRICT_B_FAILURES_EXPLICIT',revision=queue['revision'],phase_count=18,
    standard_A_pass=18,strict_B_status_counts=dict(Counter(x['status'] for x in sources if x['mode']=='B')),
    strict_B_error_count=sum(x['errors'] for x in failures),strict_B_failing_declaration_count=sum(len(x['declarations']) for x in failures),
    controls_pass=102,negative_controls_exactly_one_error=34,positive_controls_zero_errors=68,
    stored_own_constants=own_count,stored_own_axiom_union=sorted(axioms),all_stored_own_axioms_standard_subset=True,
    snapshots_checked=18,collectors_checked=18,resource_retries=0,source_hashes_unchanged=True,
    source_seals_status_counts=dict(Counter(x['status'] for x in sources)),
    all_source_seals_pass=not failures,phases=phases,strict_B_failures=failures,
    native_summary=str(folder/'summary.json'),queue=str(queue_path),tool_sha256=sha(Path(__file__).read_bytes()))
for name,value in [('native-totals.json',result),('strict-b-failures.json',failures)]:
    destination=folder/name
    assert not destination.exists()
    destination.write_text(json.dumps(value,indent=2)+'\n')
(folder/'summarize_final18_native.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({k:v for k,v in result.items() if k not in ('phases','strict_B_failures')},indent=2))
