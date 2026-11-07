from pathlib import Path
import json,re,hashlib
OUT=Path(__file__).resolve().parent
ctx=json.loads((OUT/'context.json').read_text());changes=json.loads((OUT/'changes.json').read_text());guards=set((OUT/'guard-definitions.txt').read_text().splitlines())
metadata={};allroots=[];allselected=[];foreign=[];cited=[];runs=[]
for tag,wanted in [('SAT',5),('Hardness',8)]:
 mode_data={}
 for mode in ['native','sealed']:
  name=tag+'-final-'+mode;receipt=json.loads((OUT/(name+'-run.json')).read_text());assert (receipt['exit'],receipt['errors'])==(0,0),name
  raw=(OUT/(name+'.out')).read_text();source=(OUT/(name+'.lean.txt')).read_text()
  assert hashlib.sha256(source.encode()).hexdigest()==receipt['input_sha256']
  assert hashlib.sha256(raw.encode()).hexdigest()==receipt['output_sha256']
  roots=[{'name':n,'private':b=='true'} for n,b in re.findall(r'^ROOT\|([^|]+)\|private=(\w+)',raw,re.M)];assert len(roots)==wanted and all(r['private'] for r in roots)
  axs=[{'name':n,'kind':k,'axioms':[x.strip() for x in a.split(',') if x.strip()]} for n,k,a in re.findall(r'^PROOFAX\|([^|]+)\|kind=([^|]+)\|\[([^\]]*)\]',raw,re.M)]
  assert all(set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in axs)
  fs=[dict(zip(['root','name','owner','hints'],x)) for x in re.findall(r'^FOREIGNDEF\|([^|]+)\|([^|]+)\|([^|]+)\|hints=(\w+)$',raw,re.M)]
  cs=[dict(zip(['root','name','owner','kind','private'],x)) for x in re.findall(r'^CITED\|([^|]+)\|([^|]+)\|([^|]+)\|kind=([^|]+)\|private=(\w+)$',raw,re.M)]
  assert not [r for r in cs if r['private']=='true'],name
  assert {r['name'] for r in fs if r['hints']=='regular'}<=guards
  # Locate every actual changed theorem's complete source region to classify warnings.
  warnings=[];changed_warnings=[];ranges=[]
  for r in changes:
   if ('SAT' if r['file'].endswith('/SAT.lean') else 'Hardness')!=tag:continue
   token=r['new_doc']+'\n'+r['header']+'\n'+r['new_body'];a=source.index(token);start=source[:a].count('\n')+1;end=start+token.count('\n');ranges.append((start,end,r['name']))
  for line,col,text in re.findall(r'^.*?:(\d+):(\d+): warning: (.*)$',raw,re.M):
   row={'line':int(line),'column':int(col),'text':text};warnings.append(row)
   if any(a<=int(line)<=b for a,b,n in ranges):changed_warnings.append(row)
  assert not changed_warnings,name
  mode_data[mode]={'roots':roots,'proofAX':axs,'foreign_definitions':fs,'CITED':cs,'warnings':warnings,'warnings_in_changed_sections':changed_warnings,'guard_count':len(guards)}
  runs.append({'name':name,**{k:receipt[k] for k in ['exit','errors','seconds','input_sha256','output_sha256']},'warnings':len(warnings)})
 assert {x['name'] for x in mode_data['native']['proofAX']}=={x['name'] for x in mode_data['sealed']['proofAX']}
 assert {(x['name'],x['kind'],tuple(x['axioms'])) for x in mode_data['native']['proofAX']}=={(x['name'],x['kind'],tuple(x['axioms'])) for x in mode_data['sealed']['proofAX']}
 metadata[tag]=mode_data;allroots+=mode_data['sealed']['roots'];allselected+=mode_data['sealed']['proofAX'];foreign+=mode_data['sealed']['foreign_definitions'];cited+=mode_data['sealed']['CITED']
assert len(allroots)==13 and len(allselected)==18
checks=json.loads((OUT/'control-check.json').read_text());assert checks['definitions']==18 and checks['pointwise_and_abstracted_pairs']==36 and checks['all_exact_multiplicities_match']
source=json.loads((OUT/'source-freeze.json').read_text())
for rel,r in ctx['files'].items():assert hashlib.sha256(Path(ctx['worktree'],rel).read_bytes()).hexdigest()==r['after_sha256']
(OUT/'compiled-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
summary={'status':'Authorized13 actual source repairs PASS bounded full-module/native/scoped-seal/controls; not integrated replay/gate clearance','source_repairs':13,'doc_updates':7,'source_additions_removals':0,'root_count':len(allroots),'compiled_descendants':len(allselected)-len(allroots),'all18_selected_standard_AX':True,'foreign_ordinary_definitions':sorted({r['name'] for r in foreign if r['hints']=='regular'}),'all_ordinary_guarded':True,'abbrev_projection_exclusions':sorted({r['name'] for r in foreign if r['hints']=='abbrev'}),'direct_CITED_owners':sorted({r['owner'] for r in cited}),'no_direct_imported_private_reference':True,'guard_definitions':18,'paired_controls':36,'controls_exact':True,'all_old_source_headers_imports_attrs_order_defs_and_other_bodies_frozen':True,'source_stable_at_final_check':True,'native_sealed_source_guard_only_difference':True,'native_sealed_constant_names_kinds_AX_match':True,'runs':runs,'no_warning_in_any_changed_section':True,'initial_Hardness_native_metadata_attempt_exit1_retained':True,'other_remaining_candidates':'remaining-assessment.md; no additional changes/debt/API/import approval','complete_snapshot_input':'parent supplied complete oleans-msg4; plain runs produce no compiled output','full_integrated_replay_NOT_RUN':True,'screens_NOT_RUN':True,'Git_commit_push_NOT_RUN':True}
(OUT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['root_count','compiled_descendants','foreign_ordinary_definitions','guard_definitions','paired_controls','no_warning_in_any_changed_section']},indent=2))
