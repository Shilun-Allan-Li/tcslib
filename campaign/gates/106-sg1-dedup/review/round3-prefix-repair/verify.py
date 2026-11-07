from pathlib import Path
import json,re,hashlib
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((OUT/'context.json').read_text());ch=json.loads((OUT/'change.json').read_text());before=(OUT/'Hardness-before.lean.txt').read_text();after=(OUT/'Hardness-after.lean.txt').read_text()
old=ch['old_doc']+'\n'+ch['header']+'\n'+ch['old_body'];new=ch['new_doc']+'\n'+ch['header']+'\n'+ch['new_body'];assert after.count(new)==1
reversed_source=after.replace(new,old).replace(ch['new_import']+'\n','',1);assert reversed_source==before
assert sha(Path(c['worktree'],c['owned_file']))==c['after_sha256']==sha(OUT/'Hardness-after.lean.txt')
assert not re.search(r'\b(sorry|admit|unsafe|unfold|change)\b',ch['new_body']) and 'eq_def' not in ch['new_body']
assert before.count('sorry')==after.count('sorry')==0
for folder in ['round3-closure-repairs','round3-extra-repairs']:
 p=OUT.parent/folder;m=json.loads((p/'MANIFEST.json').read_text())
 for row in m['files']:
  f=p/row['path'];assert f.stat().st_size==row['bytes'] and sha(f)==row['sha256']
sealed=(OUT/'Hardness-sealed-v1.lean.txt').read_text();native=(OUT/'Hardness-native-v1.lean.txt').read_text();wrapper='section SG1PrefixSeal\n'+(OUT/'guard-attributes.txt').read_text()+new+'end SG1PrefixSeal\n';assert sealed.count(wrapper)==1 and sealed.replace(wrapper,new)==native
metadata={};runs=[];guards=set((OUT/'guard-definitions.txt').read_text().splitlines());assert len(guards)==21
for name in ['Preapply-sealed-v1','Hardness-native-v1','Hardness-sealed-v1']:
 r=json.loads((OUT/(name+'-run.json')).read_text());s=(OUT/(name+'.out')).read_text();src=(OUT/(name+'.lean.txt')).read_text();assert (r['exit'],r['errors'])==(0,0),name
 assert sha(OUT/(name+'.lean.txt'))==r['input_sha256'] and sha(OUT/(name+'.out'))==r['output_sha256']
 roots=re.findall(r'^ROOT\|([^|]+)\|private=(\w+)',s,re.M);assert len(roots)==1 and roots[0][1]=='true'
 ax=[{'name':n,'kind':k,'axioms':[x.strip() for x in a.split(',') if x.strip()]} for n,k,a in re.findall(r'^PROOFAX\|([^|]+)\|kind=([^|]+)\|\[([^\]]*)\]',s,re.M)];assert len(ax)==1 and set(ax[0]['axioms'])<={'propext','Classical.choice','Quot.sound'}
 fs=[dict(zip(['root','name','owner','hints'],row)) for row in re.findall(r'^FOREIGNDEF\|([^|]+)\|([^|]+)\|([^|]+)\|hints=(\w+)$',s,re.M)];assert {x['name'] for x in fs if x['hints']=='regular'}<=guards
 cites=[dict(zip(['root','name','owner','kind','private'],row)) for row in re.findall(r'^CITED\|([^|]+)\|([^|]+)\|([^|]+)\|kind=([^|]+)\|private=(\w+)$',s,re.M)];assert all(x['private']=='false' for x in cites)
 pos=src.index(new);lo=src[:pos].count('\n')+1;hi=lo+new.count('\n');warnings=[{'line':int(a),'column':int(b),'text':t} for a,b,t in re.findall(r'^.*?:(\d+):(\d+): warning: (.*)$',s,re.M)];assert not [w for w in warnings if lo<=w['line']<=hi]
 metadata[name]={'roots':roots,'AX':ax,'foreign_definitions':fs,'CITED':cites,'warnings':warnings,'changed_section_warning_count':0}
 runs.append({'name':name,**{k:r[k] for k in ['exit','errors','seconds','input_sha256','output_sha256']},'warnings':len(warnings)})
assert metadata['Hardness-native-v1']['AX']==metadata['Hardness-sealed-v1']['AX']
reader=(OUT/'Serialized-reader-before-v1.out').read_text();assert 'BEFORE_ANY_REFERENCE|Complexity.PrefixByLength.drop.eq_1|owner=TCSlib.Complexity.ClassNP.PolyTimePrefix|kind=theorem|private=false|AX=[]' in reader
assert 'Eq.refl' in reader
controls=json.loads((OUT/'control-check.json').read_text());assert controls['definitions']==21 and controls['pointwise_and_abstracted_pairs']==42 and controls['all_exact_multiplicities_match']
graph=json.loads((OUT/'import-closure-delta.json').read_text());assert graph['TCSlib_before_count']==45 and graph['TCSlib_after_count']==51 and graph['TCSlib_added_count']==6 and not graph['TCSlib_removed'];assert not graph['full_source_import_closure_including_Core_packages']['compiled_modules_missing']
# Snapshot and module-source inputs already pinned by full closure analysis remain byte-identical.
for m,row in graph['TCSlib_pins'].items():assert sha(Path(row['source']))==row['source_sha256'] and sha(Path(row['olean']))==row['olean_sha256']
(OUT/'compiled-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
summary={'status':'One approved import and exact Drop repoint; final full native/scoped seal PASS; combined16 metadata/replay remains parent work','authorized_source':'Hardness only','approved_single_import':c['approved_import'],'exact_old_source_recovered_by_reversing_only_one_import_one_body_one_doc':True,'all_other_headers_imports_attrs_order_defs_and_other_bodies_frozen':True,'source_sha256':c['after_sha256'],'source_stable_at_final_check':True,'prior15_review_payloads_unchanged':True,'full_final_native_covers_prior_unused_simp_cleanup':True,'new_actual_root_count':1,'compiled_descendants':0,'all_selected_standard_AX':True,'guard_count':21,'fresh_paired_controls':42,'serialized_public_reader_present_before_any_reference':True,'reader_AX':[],'direct_ordinary_defs':sorted({x['name'] for x in metadata['Hardness-sealed-v1']['foreign_definitions'] if x['hints']=='regular'}),'direct_CITED_owners':sorted({x['owner'] for x in metadata['Hardness-sealed-v1']['CITED']}),'no_direct_imported_private_reference':True,'no_warning_in_changed_section':True,'native_sealed_guard_removal_identity':True,'native_sealed_AX_same':True,'TCSlib_import_closure_delta':[45,51,6],'full_source_Core_package_closure_delta':[2732,2738,6],'all_new_imports_present_in_snapshot_no_fetch':True,'runs':runs,'no_compiledoutput_cache_snapshot_Git_commit_push_screen_changes':True,'combined16_metadata_replay':'NOT RUN; parent work'}
(OUT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['source_sha256','new_actual_root_count','compiled_descendants','guard_count','fresh_paired_controls','direct_CITED_owners','TCSlib_import_closure_delta']},indent=2))
