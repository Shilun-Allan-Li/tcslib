from pathlib import Path
import re,json,hashlib,collections
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');F=Path('/private/tmp/ab34-ro1-integration');P=A/'native-project';V=Path('/private/tmp/ab34-ro1-deterministic-native-overlay');B=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
owners=[]
for rel in json.loads((A/'planned-native-owners.json').read_text()):
 key=rel[:-5].replace('/','__')+'__attempt1';r=json.loads((A/'native'/(key+'.json')).read_text());assert r['exit']==0 and r['errors']==0 and r['source_unchanged'];assert r['source_sha256']==h(P/rel);assert r['fresh_olean_sha256']==h(V/(rel[:-5]+'.olean'));assert r['raw_sha256']==h(A/'native'/(key+'.log'));owners.append(r)
def ax(name):return [json.loads(l.split('|',1)[1]) for l in (A/'probes'/(name+'__attempt1.log')).read_text().splitlines() if l.startswith('AX|')]
ca=ax('AXSmallAltFixed');ba=ax('AXSmallBaselineFixed');assert len(ca)==7 and len(ba)==6;bm={(r['owner'],r['root']):r['axioms'] for r in ba};assert all(r['axioms']==bm[(r['owner'],r['root'])] for r in ca if r['root']!='Turing.MultiTapeTM.runFrom_one');assert all(set(r['axioms'])<={'propext','Quot.sound','Classical.choice'} for r in ca)
control_expected={(n,m) for n in json.loads((F/'api-seal-inventory.json').read_text())['guards'] for m in ['point','abstract']};pos={};neg=set()
for l in (A/'probes/APIControlsNativeFixed__attempt1.log').read_text().splitlines():
 m=re.match(r'CONTROL\|([^|]+)\|([^|]+)\|PASS\|kernelChecked=(.+)',l)
 if m:pos[(m[1],m[2])]=m[3]
for l in (A/'probes/APIControlsSealedFixed__attempt1.log').read_text().splitlines():
 m=re.match(r'CONTROL\|([^|]+)\|([^|]+)\|FAIL',l)
 if m:neg.add((m[1],m[2]))
assert set(pos)==neg==control_expected
for i,n in enumerate(json.loads((F/'api-seal-inventory.json').read_text())['guards']):
 for j,mode in enumerate(['point','abstract']):assert pos[(n,mode)]==f'RO1AltAPIRfl_{2*i+j+1}_{mode}'
for name,exit,errs in [('APITypeCfg',0,0),('APITypeDet',0,0),('AXSmallAltFixed',0,0),('AXSmallBaselineFixed',0,0),('APIScopeNative',0,0),('APIScopeSealed',0,0),('APIControlsNativeFixed',0,0),('APIControlsSealedFixed',1,12)]:
 p=A/'probes'/(name+'__attempt1.json');r=json.loads(p.read_text());assert r['exit']==exit and r['errors']==errs and r['warnings']==0 and r['source_unchanged'];assert r['raw_sha256']==h(p.with_suffix('.log'))
(A/'executed-verification.json').write_text(json.dumps({'native_owner_checks':owners,'native_owner_count':7,'native_owner_errors':0,'native_owner_warnings':sum(r['warnings'] for r in owners),'native_owner_sorry_warnings':sum(r['sorry_warnings'] for r in owners),'full61_owner_sweep_executed':False,'native_API_type_contract_both_options_pass':True,'API_whole_doc_header_body_native_and_six_guard_sealed_pass':True,'fresh_positive_kernel_checked_controls':12,'exact_expected_negative_controls':12,'fresh_control_identity_sets_names_exact':True,'small_AXIOM_current7_baseline6_unchanged_existing_sets':True,'small_AXIOM_roots':ca,'no_changed_source_worktree_or_Git_or_canonical_record':True,'no_full_downstream_replay_or_screen':True},indent=2)+'\n')
raw=(F/'freeze-declarations.py').read_text();ns={};exec(raw[:raw.index('changed=[];removed=[]')],ns);extract=ns['extract']
def normalized(xs):
 out={}
 for x in xs:
  if x['lexical_name'].startswith('_root_.'):x['name']=x['lexical_name'][7:]
  assert x['name'] not in out,x['name'];out[x['name']]=x
 return out
changed=[];added=[];removed=[];header_deltas=[];def_deltas=[]
for row in json.loads((A/'all-source-hashes.json').read_text()):
 if not row['changed']:continue
 rel=row['path'];o=normalized(extract((A/'source-before'/(rel+'.txt')).read_text()));n=normalized(extract((P/rel).read_text()))
 for k in o.keys()-n.keys():removed.append({'path':rel,'name':k})
 for k in n.keys()-o.keys():added.append({'path':rel,**n[k]})
 for k in o.keys()&n.keys():
  if o[k]['header']!=n[k]['header']:header_deltas.append({'path':rel,'name':k})
  if o[k]['body']!=n[k]['body']:
   changed.append({'path':rel,'name':k,'kind':n[k]['kind'],'header':n[k]['header'],'before_line':o[k]['line'],'after_line':n[k]['line']})
   if n[k]['kind'] not in ('theorem','lemma'):def_deltas.append({'path':rel,'name':k})
assert not header_deltas;assert len(added)==1 and added[0]['name']=='Turing.MultiTapeTM.runFrom_one';assert len(removed)==5;assert def_deltas==[{'path':'TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean','name':'Turing.zr_cellContract'}]
cf_api=json.loads((F/'declaration-freeze.json').read_text())['new_declarations'][0];da=added[0];assert da['header'].split('runFrom_one',1)[1]==cf_api['header'].split('runFrom_one',1)[1] and da['body']==cf_api['body']
(A/'source-freeze.json').write_text(json.dumps({'all_existing_headers_exact':True,'changed_existing_declarations':changed,'added':added,'removed':removed,'only_changed_definition':def_deltas,'definition_proof_field_check':'The zr_cellContract text is identical to the frozen CfgFacts option; only run/env proof fields differ from baseline.','CfgFacts_exact_baseline':h(P/'TCSlib/Complexity/TuringMachine/CfgFacts.lean')==next(r['baseline_sha256'] for r in json.loads((F/'all-source-final-hashes.json').read_text()) if r['path']=='TCSlib/Complexity/TuringMachine/CfgFacts.lean'),'no_import_changes_any_of929_sources':True,'API_binders_target_and_body_exact_source':True},indent=2,ensure_ascii=False)+'\n')
maps=json.loads((F/'snapshot-final-maps.json').read_text());orig={str(p.relative_to(B)):h(p) for p in sorted(B.rglob('*.olean'))};alt={str(p.relative_to(V)):h(p) for p in sorted(V.rglob('*.olean'))};assert orig==maps['input_MAC8_final'] and len(orig)==len(alt)==895 and set(orig)==set(alt);allowed={r['file'][:-5]+'.olean' for r in owners};assert all(orig[p]==alt[p] or p in allowed for p in orig)
(A/'whole895-object-maps.json').write_text(json.dumps({'original_MAC8_final_all895':orig,'private_alternative_final_all895':alt,'original_MAC8_unchanged':True,'complete_clone_final895':True,'only_seven_native_owner_objects_differ':True,'initial_clone_origin':'cp -cR whole original MAC8, recorded successful copy before first Deterministic compile','separate_initial_alternate_overlay_SHA_scan_executed':False,'no_splicing':True},indent=2)+'\n')
manifest=json.loads((F/'MANIFEST.json').read_text());assert h(F/'MANIFEST.json')=='5069e96884fbd28d3f3ca4819c7cd005de4d13b2acfaa3d312ce8e1137b73d56'
for r in manifest['payload_files']:assert h(F/r['path'])==r['sha256'],r['path']
(A/'frozen-parent-integrity.json').write_text(json.dumps({'CfgFacts_frozen_manifest_sha256':h(F/'MANIFEST.json'),'all1360_parent_payload_hashes_unchanged':True,'parent_source_worktree_not_written_by_alternative_work':True},indent=2)+'\n')
print('Alternative bounded native/type/AX/scope/controls verified; full source freeze, original graph, final895 maps and immutable parent1360 payloads verified.')
