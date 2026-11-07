"""Verify exact unchanged source blocks for all observed S2 native seal failures."""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
parser_path=root/'repairs/inherited-full-survey-reproduce.py'
spec=importlib.util.spec_from_file_location('reviewed_source_parser',parser_path)
parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
e=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/fills/shared-lemmas/s2/final/maintainer-rule10')
run=e/'native-seal-runs/r1'
summary=json.loads((run/'summary.json').read_text())
assert summary['valid_harnesses']==10 and summary['harness_failures']==0
assert all(c['comparison_valid'] and not c['head_only'] and not c['base_only'] for c in summary['comparisons'])
rows=[]
for module in sorted({r['module'] for r in summary['results']}):
    pair={r['role']:r for r in summary['results'] if r['module']==module}
    raw={role:Path(r['raw_source']).read_bytes() for role,r in pair.items()}
    for role in pair:
        assert hashlib.sha256(raw[role]).hexdigest()==pair[role]['source_sha256']
    decls={role:parser.parse(value.decode()) for role,value in raw.items()}
    names={e['qualified_source_name'] for e in pair['Head']['errors']}
    assert names=={e['qualified_source_name'] for e in pair['Base']['errors']}
    for name in sorted(names):
        blocks={role:[d for d in ds if d['canonical']==name] for role,ds in decls.items()}
        assert all(len(v)==1 for v in blocks.values()),name
        head,base=blocks['Head'][0],blocks['Base'][0]
        assert head['raw']==base['raw'],name
        assert head['scope_stack']==base['scope_stack'] and head['context_commands']==base['context_commands'],name
        diagnostics={role:[v for v in r['errors'] if v['qualified_source_name']==name] for role,r in pair.items()}
        for role,block in [('Head',head),('Base',base)]:
            assert all(block['start']<=v['source_line']<=block['end'] for v in diagnostics[role])
        rows.append({'module':module,'qualified_source_name':name,
                     'head_range':[head['start'],head['end']], 'base_range':[base['start'],base['end']],
                     'unchanged_raw_header_body_sha256':hashlib.sha256(head['raw'].encode()).hexdigest(),
                     'diagnostics':diagnostics,'classification':'UNCHANGED_BASE_PROOF_FAILURE_NOT_A_PASS'})
assert len(rows)==5
result={'head':summary['head'],'base':summary['base'],'valid_harnesses':10,'harness_failures':0,
        'inherited_failing_declarations':5,'head_diagnostics':sum(len(r['errors']) for r in summary['results'] if r['role']=='Head'),
        'base_diagnostics':sum(len(r['errors']) for r in summary['results'] if r['role']=='Base'),
        'head_only_failing_declarations':0,'new_or_touched_failure_observed':False,
        'base_olean_tree_rebuilt':False,'imported_environment_revision':summary['head'],
        'scope':'Every failing complete header/body and binding context is byte-identical to base; failures remain recorded as debt.',
        'limit':'Base source copies use current imported head objects. No cold baseline environment or whole-file pass is claimed.',
        'source_parser_sha256':hashlib.sha256(parser_path.read_bytes()).hexdigest(),'rows':rows}
dest=run/'source-failure-reconciliation.json'
assert not dest.exists();dest.write_text(json.dumps(result,indent=2)+'\n')
(run/'reconcile_s2_seals.py').write_bytes(Path(__file__).read_bytes())
(run/'source-parser.source.txt').write_bytes(parser_path.read_bytes())
print(json.dumps({k:v for k,v in result.items() if k not in ('rows','source_parser_sha256')}))
