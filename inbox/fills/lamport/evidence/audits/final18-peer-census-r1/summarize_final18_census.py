"""Summarize independently checked all18 native censuses/request sets; no Lean."""
import hashlib
import json
from pathlib import Path
HERE=Path(__file__).parent
EVIDENCE=HERE.parent.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
source=HERE/'batch006.json'
data=json.loads(source.read_text())
assert data['overlay_pass'] and data['native_censuses_completed']==data['request_sets_completed']==data['phases_requested']==18 and not data['issue_phases']
rows=[]
for record in data['phases']:
    assert record['native_census']==record['request_coverage']=='PASS'
    assert all(record['census_tests'].values()) and not record['nonstandard_axioms']
    log=(EVIDENCE/record['collector_log']).read_text()
    closure=int(next(line.rsplit('\t',1)[1] for line in log.splitlines() if line.startswith('LAMP-CLOSURE-EXACT\t')))
    modes={r['mode']:r['actual_requests'] for r in record['mode_reviews']}
    rows.append(dict(phase=record['phase'],target=record['target'],exact_foreign_closure=closure,
        own_stored_constants=record['own_stored_constants'],own_axioms='SUBSET_OF_Classical.choice_Quot.sound_propext',
        own_axiom_set_counts=record['own_axiom_set_counts'],A_requests=modes['A'],B_requests=modes['B'],
        eligible_private_names=record['eligible_private_names'],eligible_matchers=record['eligible_matchers'],
        collector_log=record['collector_log'],collector_log_sha256=record['collector_log_sha256'],official_census=record['official_census'],
        request_manifest=record['source_request_manifest'],request_manifest_sha256=record['source_request_manifest_sha256']))
payload=dict(scope='All18 completed native census and exact eligible request-set tuples only. A/B source-seal outcomes and control diagnostics are separately reviewed; no B pass is inferred from this report.',
    revision=data['revision'],independent_audit='batch006.json',independent_audit_sha256=sha(source.read_bytes()),
    all18_census_and_requests_PASS=True,total_own_stored_constant_rows=sum(r['own_stored_constants'] for r in rows),
    all_own_axiom_sets_standard3_subsets=True,rows=rows,tool_sha256=sha(Path(__file__).read_bytes()))
output=HERE/'final18-census-summary-r1.json'
assert not output.exists();output.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({key:payload[key]for key in ['all18_census_and_requests_PASS','total_own_stored_constant_rows','all_own_axiom_sets_standard3_subsets']},indent=2))
print('B counts',','.join(str(r['B_requests'])for r in rows))
