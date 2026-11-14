"""Regenerate completed cached native probes from candidate pure functions only.
No Lean, no generator top-level execution, no active evidence writes.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
HERE=Path(__file__).parent
EVIDENCE=HERE.parent.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
load=lambda path:json.loads(path.read_text())
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',required=True)
args=parser.parse_args()
assert Path(args.output).name==args.output and args.output.endswith('.json')
output=HERE/args.output
assert not output.exists()
queue_path=EVIDENCE/'preparation/final18-r2/cached-collectors-r3/queue.json'
queue=load(queue_path)
generator=Path(queue['prepare_tool'])
generator_raw=generator.read_bytes()
assert sha(generator_raw)=='35d744b699ebc16a198eea51336e5ef0b261a487a0df946857be1715e4e0f9db'
tree=ast.parse(generator_raw.decode())
allowed={'lean_string','blank_comments','imports','parse_catalog','seal_command','instrument'}
namespace={'json':json,'re':re}
nodes=[node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name in allowed]
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(generator)+':pure-functions-only','exec'),namespace)
make=next(node for node in tree.body if isinstance(node,ast.FunctionDef) and node.name=='make_seals')
control_block=next(node for node in make.body if isinstance(node,ast.If) and isinstance(node.test,ast.Name) and node.test.id=='ordinary')
def literals(block):
    out={}
    for node in block:
        if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in {'negative','positive','sensitivity_symbol'}:
            out[node.targets[0].id]=ast.literal_eval(node.value)
    return out
ordinary=literals(control_block.body)
fallback=literals(next(node for node in control_block.body if isinstance(node,ast.If)).body)
phases=[]
for record in queue['records'][4:]:
    phase=record['phase']
    summary_path=EVIDENCE/'logs/final18-native-r3'/phase/'summary.json'
    row=dict(phase=phase,status='PENDING_COMPLETED_PHASE')
    if not summary_path.exists():phases.append(row);continue
    summary=load(summary_path)
    prep=load(Path(record['manifest']))['records'][0]
    raw= (Path(record['phase_directory'])/prep['raw_source']).read_bytes()
    catalog,_=namespace['parse_catalog'](Path(summary['collector_attempts'][-1]['raw_log']))
    eligible=sorted([r for r in catalog[record['target']] if r['home']!=prep['snapshot_module'] and r['is_definition'] and not r['instance'] and r['status']!='reducible'],key=lambda r:r['spelling'])
    literal=ordinary if any(r['spelling']=='Complexity.NUPPT.inArg' for r in catalog[record['target']]) else fallback
    attempts=[]
    for attempt_name in summary['seals']['attempts']:
        folder=Path(attempt_name)
        manifest_raw=(folder/'seal-manifest.json').read_bytes()
        manifest=json.loads(manifest_raw)
        provenance=load(folder/'actual-generator-provenance.json')
        tests={
            'actual_candidate_generator_hash':sha((folder/provenance['actual_generator_copy']).read_bytes())==provenance['actual_generator_sha256']==sha(generator_raw),
            'actual_candidate_generator_path':provenance['actual_generator_path']==str(generator),
            'actual_manifest_hash':provenance['native_attempt_manifest_sha256']==sha(manifest_raw),
        }
        probes=[]
        for probe in manifest['probes']:
            label=probe['label'];control=bool(probe.get('control'))
            mode=probe['mode'] if not control else re.fullmatch(phase+r'_Control([AB])(Unsealed|Negative|Reader)',label).group(1)
            selected=[r for r in eligible if mode=='B' or r['spelling']!='Complexity.PolyExpr.eval']
            if not control:
                text,mapping=namespace['instrument'](raw,label,selected)
                map_check=mapping==probe['original_line_map']
            else:
                kind=re.fullmatch(phase+r'_Control[AB](Unsealed|Negative|Reader)',label).group(1)
                text='import Lean\n'+''.join('import '+name+'\n' for name in namespace['imports'](raw))+'\nset_option maxHeartbeats 0\n'
                if kind!='Unsealed':text+=namespace['seal_command'](label,selected)
                text+=literal['positive' if kind=='Reader' else 'negative']
                if kind!='Unsealed':text+=namespace['seal_command'](label,selected,verify=True)
                map_check=True
            actual_path=folder/'sources'/(label+'.lean')
            if not actual_path.exists():
                probes.append(dict(label=label,status='PENDING_CHECKED_SOURCE_CAPTURE'));continue
            actual=actual_path.read_bytes()
            expected_rows=[] if control and label.endswith('Unsealed') else selected
            result_path=folder/(label+'.result.json')
            probe_tests={
                'retained_source_exact_candidate_pure_regeneration':actual==text.encode(),
                'retained_source_manifest_hash':sha(actual)==probe['probe_sha256'],
                'catalog_request_rows_exact':probe['requests']==expected_rows,
                'original_source_bound':sha(raw)==prep['source_sha256'],
                'line_map_exact_candidate':map_check,
                'native_result_same_source_hash':result_path.exists() and load(result_path)['source_sha256']==sha(actual),
            }
            probes.append(dict(label=label,status='PASS' if all(probe_tests.values()) else 'ISSUE',tests=probe_tests,source_sha256=sha(actual),request_count=len(expected_rows)))
        attempts.append(dict(path=attempt_name,tests=tests,probes=probes,passed=all(tests.values()) and all(r['status']=='PASS' for r in probes)))
    row.update(status='PASS' if all(r['passed'] for r in attempts) else 'ISSUE',attempts=attempts,regenerated_probes=sum(len(r['probes']) for r in attempts))
    phases.append(row)
payload=dict(scope='Exact source-only regeneration for completed remaining14 cached phases; first4 old generator adoption audited separately. No Lean executed. No pending-phase claim.',queue_sha256=sha(queue_path.read_bytes()),generator_sha256=sha(generator_raw),phases=phases,completed_pass=sum(r['status']=='PASS' for r in phases),issue_phases=[r['phase'] for r in phases if r['status']=='ISSUE'],tool_sha256=sha(Path(__file__).read_bytes()))
output.write_text(json.dumps(payload,indent=2)+'\n')
(HERE/(output.stem+'.tool.py')).write_bytes(Path(__file__).read_bytes())
print(json.dumps({key:payload[key] for key in ['completed_pass','issue_phases']},indent=2))
for row in phases:
 if row['status']=='PASS':print(row['phase'],row['regenerated_probes'])
