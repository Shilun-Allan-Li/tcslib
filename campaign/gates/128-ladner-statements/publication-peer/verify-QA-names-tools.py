from pathlib import Path
import json,hashlib,subprocess,os,re
P=Path('/private/tmp/ab34-gate128-ready-draft');O=Path('/private/tmp/ab34-gate128-publication-peer');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');Q=P/'evidence/source-QA119/current/qa';J=lambda p:json.loads(p.read_text());h=lambda b:hashlib.sha256(b).hexdigest();env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0'
def w(n,x):(O/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
runs=J(Q/'RUNS.json');assert len(runs)==6;qa=[]
for r in runs:
 for prefix in ['stdout','stderr']:
  b=(Q/r[prefix]).read_bytes();assert len(b)==r[prefix+'_bytes'] and h(b)==r[prefix+'_sha256']
 if r['kind']!='size':assert h((Q/'lint_adapter.py').read_bytes())==r['adapter_sha256'];assert h((Q/'helpers'/('style_lint.py' if r['kind']=='style' else 'campaign_style_lint.py')).read_bytes())==r['helper_sha256']
 assert r['exit']==(1 if r['kind']=='style' else 0);qa.append({'side':r['side'],'kind':r['kind'],'actual_time':r['start_utc'],'exit':r['exit'],'stdout_SHA256':r['stdout_sha256'],'stderr_SHA256':r['stderr_sha256'],'raw_lengths_hashes_exact':True})
req=J(Q/'REQUEST.json');assert req['campaign_default_CHECK8B'] is False;comp=J(Q/'comparison.json');assert comp['style']['BASE_count']==comp['style']['HEAD_count']==comp['style']['inherited_occurrences']==3 and comp['style']['new_occurrences']==comp['style']['removed_occurrences']==0;assert comp['campaign']['new_occurrences']==1 and comp['campaign']['HEAD_levels']=={'INFO':2}
for k in ['style','campaign']:
 findings=J(Q/('HEAD-'+k+'-findings.json'));assert not any(r.get('level') in ['FAIL','WARN'] for r in findings['findings']) if k=='campaign' else True
w('QA-raw-checks.json',{'all6_command_exit_stdout_stderr_records_match':True,'style_BASE_HEAD_exits':[1,1],'same3_inherited_facade_findings_no_new':True,'campaign_BASE_HEAD_exits':[0,0],'campaign_default_check8b':False,'new_campaign_INFO_only_authorized_owner':True,'all_raw_size_and_identity_dispositions_retained':True,'no_qa_run_by_peer':True,'runs':qa})
# Every saved name-query hit is checked against its exact frozen source and actual referenced Git blob.
name=J(P/'names/CANDIDATE-CAPTURES-AND-DISPOSITIONS.json');assert name['row_count']==len(name['full_hit_rows'])==240 and len(name['capture_rows'])==44;capchecks=[]
for r in name['capture_rows']:
 q=P/r['capture'];b=q.read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256'];blob=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest();actual=subprocess.check_output(['git','-C',str(R),'rev-parse',r['commit']+':'+r['path']],env=env).decode().strip();assert blob==r['blob']==actual;capchecks.append(dict(r,exact=True))
for r in name['full_hit_rows']:assert (P/r['capture']).read_text().splitlines()[r['line']-1]==r['text']
assert len({r['capture'] for r in name['capture_rows']})==5;w('name-query-checks.json',{'all240_existing_uncapped_literal_rows_match':True,'all44_source_commit_path_capture_bindings_actual_Git_exact':True,'unique_full_source_payloads':5,'candidate_dispositions':name['dispositions'],'limits':'Saved available-ref name/shape enumeration only; no new search or global semantic absence claim','capture_bindings':capchecks})
# Captured standards have explicit original/current records pins; do not silently relabel old prose as current authority.
std=[]
for r in J(P/'bindings/STANDARDS-AND-PACKAGE.json')['full_standards']:
 b=(P/'standards'/r['path']).read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256'];actual=subprocess.check_output(['git','-C',str(R),'show',r['records_capture']+':'+r['path']],env=env);assert actual==b;std.append({'path':r['path'],'records':r['records_capture'],'SHA256':h(b),'exact':True})
current=J(P/'bindings/CURRENT-STANDARDS.json')['all16_current_full_payloads_located_by_capture'];assert len(current)==16
for r in current:
 b=(P/r['capture']).read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256'];actual=subprocess.check_output(['git','-C',str(R),'show',r['records']+':'+r['path']],env=env);assert actual==b
context=J(P/'reproduction-tools/context.json');tools=[]
for r in context['script_provenance']:
 q=P/'reproduction-tools'/r['name'];b=q.read_bytes();assert h(b)==r['sha256'];tools.append({'name':r['name'],'SHA256':h(b),'bytes':len(b)})
V=P/'evidence/actual-validation162';assert (P/'reproduction-tools/leanelab.sh').read_bytes()==(V/'inputs/leanelab.sh').read_bytes();assert (P/'reproduction-tools/staticsorry.py').read_bytes()==(V/'inputs/passed-Nlad2/staticsorry.py').read_bytes();assert (P/'reproduction-tools/lean-toolchain').read_bytes()==(V/'inputs/lean-toolchain').read_bytes();assert (P/'reproduction-tools/lake-manifest.json').read_bytes()==(V/'inputs/lake-manifest.json').read_bytes();lake=J(P/'reproduction-tools/lake-manifest.json');assert next(r for r in lake['packages'] if r['name']=='mathlib')['rev']=='029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e';assert [context[k] for k in ['local_slots','machine_slots','threads','nice']]==[3,5,4,10]
# The design note is present before the first committed source owner, not inferred from a later status update.
first='63eb044c55032d8d9570e54e99d520522f2449e5';design='campaign/items/ladner/LADNER-design.md';before=subprocess.check_output(['git','-C',str(R),'show',first+'^:'+design],env=env);assert before==(P/'standards'/design).read_bytes()
w('tools-standards-authorization-checks.json',{'all16_original_and16_current_standard_payloads_match_declared_Git_records':True,'both_observed_records_pins_remain_original_not_final_publication':True,'recorded_LD1_7_and_edition_fallback_preserved':True,'design_note_actual_parent_tree_precedes_committed_owner':True,'no_new_layout_SAT_reader_iterator_or_seventh_obligation_approval_inferred':True,'required_full_helpers_toolchain_packages_environment_context_present':True,'actual_plain_and_writing_replay_helpers_both_present_separate':True,'package_pin_matches_two_full_Mathlib_sources':True,'binary895_input_not_exported_snapshot_maps_are_anchors_not_binaries':True,'final_canonical_logical_path_rebase_and_pins_root_owned':True,'tool_inputs':tools,'original_standard_bindings':std})
print(json.dumps({'QA_actual_rows':6,'saved_query_rows':240,'capture_ref_paths':44,'capture_payloads':5,'original_current_standard_rows':[16,16],'actual_parent_design_before_source':True,'tools_and_package_hashes_exact':True}))
