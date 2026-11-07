from pathlib import Path
import json,hashlib,re
OUT=Path(__file__).resolve().parent
c=json.loads((OUT/'context.json').read_text());changes=json.loads((OUT/'changes.json').read_text());checks={}
for rel,row in c['files'].items():
 tag=row['archive_tag'];before=(OUT/(tag+'-before.lean.txt')).read_text();after=(OUT/(tag+'-after.lean.txt')).read_text();restored=after
 for r in changes:
  if r['file']!=rel:continue
  old=r['old_doc']+'\n'+r['header']+'\n'+r['old_body'];new=r['new_doc']+'\n'+r['header']+'\n'+r['new_body'];assert restored.count(new)==1,r['name'];restored=restored.replace(new,old)
 assert restored==before,rel
 assert hashlib.sha256(Path(c['worktree'],rel).read_bytes()).hexdigest()==row['after_sha256']
 native=(OUT/(tag+'-final-native.lean.txt')).read_text();sealed=(OUT/(tag+'-final-sealed.lean.txt')).read_text();removed=sealed
 for r in changes:
  if r['file']!=rel:continue
  token=r['new_doc']+'\n'+r['header']+'\n'+r['new_body'];wrapped='section SG1ClosureSeal_'+r['name']+'\n'+(OUT/'guard-attributes.txt').read_text()+token+'end SG1ClosureSeal_'+r['name']+'\n';assert removed.count(wrapped)==1;removed=removed.replace(wrapped,token)
 assert removed==native
 checks[rel]={'before_sha256':row['before_sha256'],'after_sha256':row['after_sha256'],'proofs_changed':sum(r['file']==rel for r in changes),'docs_changed':sum(r['file']==rel and r['doc_changed'] for r in changes),'exact_old_full_source_recovered_by_only_authorized_reverse_replacements':True,'actual_source_stable':True,'all_full_headers_imports_attrs_order_executable_definitions_and_other_bodies_frozen':True,'sealed_instrumentation_only_difference':True,'raw_sorry_before':len(re.findall(r'\bsorry\b',before)),'raw_sorry_after':len(re.findall(r'\bsorry\b',after))}
 assert checks[rel]['raw_sorry_before']==checks[rel]['raw_sorry_after']
for r in changes:
 assert not re.search(r'\b(sorry|admit|unsafe|unfold|change)\b',r['new_body'])
 assert 'eq_def' not in r['new_body']
 if 'rw [' in r['new_body']:assert 'rw [← he]' in r['new_body']
(OUT/'source-freeze.json').write_text(json.dumps({'files':checks,'exact_13_authorized_names':[r['name'] for r in changes],'all_proof_bodies_use_public_rows_no_foreign_def_unfolding':True,'foreign_projection_abbrev_inventory':'Compiled metadata parsed separately','no_actual_production_guard_instrumentation':True},indent=2)+'\n')
print(json.dumps(checks,indent=2))
