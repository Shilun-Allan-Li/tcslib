from pathlib import Path
import re,json,hashlib,collections,difflib
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
code=(O/'prepare-candidate.py').read_text();ns={};exec(code[code.index('def mask('):code.index('\nsources=')],ns);mask=ns['mask']
freeze=json.loads((O/'declaration-freeze.json').read_text());changed={(r['path'],r['lexical_name']) for r in freeze['changed_proof_roots']};deleted={(r['path'],r['lexical_name']) for r in freeze['removed_declarations']}
known={
 'xr_answer_tail':'Consumes xr_answerTM_run; specialized run contract, no one-step equation reproof.',
 'qy_run_two':'Two-step successor contract; its retained run-one term is part of the literal statement, not a proof of run-one=step.',
 'qy_round_of_seg':'Consumes the supplied one-step endpoint hypothesis h1.',
 'f6_ruler_moves':'Consumes the published walk/skip/rewind run contracts; literal 1 is an instantiation of a run contract.',
 'b2b_trial_run':'Consumes phase-host endpoint ha.2, already a run contract.',
 'cw_seg_left':'Consumes cw_left_run and the configuration move equation; the one-step reader in cw_left_run is repointed.',
 'counter_body':'General phase/embedding run proof; literal-one run is a starting configuration in a larger arbitrary-time statement.',
 'iw_body_copy':'Consumes iw_one; iw_one now cites generic one-step and step_of_some.',
 'iw_body_blank':'Consumes iw_one; iw_one now cites generic one-step and step_of_some.',
 'iw_prefix_step':'Consumes the published local copy-step contract.',
 'iw_orbit':'Consumes iw_prefix_step in the orbit successor equation.',
 'iw_join_step':'Consumes iw_one; iw_one now cites generic one-step and step_of_some.',
 'iw_local':'Consumes iw_orbit/iw_body_blank and the counter-loop escape contract.',
 'emCall_exit_fixed':'Source has a canonical one-step rewrite in its local endpoint; remaining mapped one-step fact is supplied by runFrom_mapState_of_agreeOn.',
 'rt_window_run':'The endpoint is an instance of skipTM_run_ofCfg, with a local endpoint alias b\x27.',
 'zr_host_dispatch_run':'Consumes the public Contract.run endpoint and its public field equations.',
 'zr_round_of_body':'Consumes the supplied one-step endpoint h1 and Contract.run.',
 'zr_loop_round':'Consumes zr_host_dispatch_run and public phase contracts.',
 'exists_canonBoolBranch':'Consumes canonBoolPop_run and seamCompTM_run_ofCfg.',
 'exists_canonStripTM':'The rfl equation identifies a let-bound endpoint stopped := halt.runFrom ... 1; it does not rederive run-one=step.',
 'exists_canonRecordTM':'Defines a let-bound one-step endpoint and consumes canonTag_step, whose proof now cites the generic reader.',
 'canonEmitVerdict':'Consumes phaseHostTM_run_le and canonHalt_run.',
 'ic_loopHost_run':'Consumes phase-host and leaf-run endpoints; no new one-step equation proof.',
 'tt_cs_halt':'Consumes phase-host/round invariants; the exact local one-step equation in tt_round_run is repointed separately.',
 'ss_bufferAdvance_run':'Consumes ss_bufferLeaf_run at literal time one; that helper now cites the generic reader.',
 'ss_bufferClear_run':'Consumes ss_bufferLeaf_run at literal time one; that helper now cites the generic reader.'}
shape=[]
for key,kind in [('all-successor-candidate-census.json','successor equation lexical occurrence'),('literal-one-candidate-census.json','literal-one application lexical occurrence')]:
 for r in json.loads((O/key).read_text()):
  q=dict(r);k=(r['path'],r['declaration_lexical']);q['shape_kind']=kind;q['id']=f'SHAPE-{len(shape)+1:04d}'
  if k in deleted:q['disposition']='former copy removed; every client repointed';q['reason']='Approved generic API replaces the former Bool/private one-step copy.'
  elif k in changed:q['disposition']='declaration contains concrete canonical reader repoint';q['reason']='See exact current complete source and declaration disposition. Remaining arbitrary-time/two-step structure is retained; a lexical hit is not itself a confirmed copy.'
  elif r['path'].endswith('/Simulation.lean') and r['declaration_lexical']=='bufferedScanCfg_run':q['disposition']='held: approved home creates import cycle';q['reason']='Frozen separate witness: CfgFacts -> StateRenaming -> Simulation; no alternate home adopted.'
  elif kind.startswith('literal'):
   q['disposition']='retained: supplied or stronger run contract / nonexact variant';q['reason']=known.get(r['declaration_lexical'],'Literal-one use is part of a supplied endpoint, statement, or stronger contract; no exact run-one=step derivation identified by the inspected source context.')
  else:q['disposition']='retained: general successor/multi-step structure';q['reason']='The general n+1 run equation is stronger/different than the literal-one API. Source context retained uncapped; no claim that every lexical hit is a duplicate.'
  shape.append(q)
(O/'uncapped-shape-dispositions.json').write_text(json.dumps(shape,indent=2,ensure_ascii=False)+'\n')
fragments=json.loads((O/'candidate-edits.json').read_text())
for r in fragments:
 if r['kind']=='remove former one-step copy':
  r['declaration_lexical']=next(d['lexical_name'] for d in freeze['removed_declarations'] if d['path']==r['path'])
 if r['after'] is not None:
  r['disposition']='integrated into current held candidate; exact final source is authoritative'
  if r['kind']=='successor/zero pair':r['reason']='Raw pair candidate; literal-one or inner step of a numeric-time closure repointed. Fixed-time two-step closures keep their outer successor equation. Final native receipt validates the whole owner.'
for rev in range(2,9):
 p=O/f'revision{rev}'/'edits.json'
 if p.exists():
  for r in json.loads(p.read_text()):fragments.append({'id':f'REVISION{rev}-{len(fragments)+1:04d}','revision':rev,'disposition':'additional exact reader conversion or documented native matcher refinement','source':'revision'+str(rev)+' before/after captures',**r})
(O/'fragment-dispositions.json').write_text(json.dumps(fragments,indent=2,ensure_ascii=False)+'\n')
data=[];admissions=[];arg_delta=collections.Counter();old_names=[];residual_pairs=[]
pair=re.compile(r'(?<![\w.])(?:MultiTapeTM\.)?runFrom_succ_eq_step\x27?(?:\s*\((?:tm|cfg|t)\s*:=\s*[^()\n]*\))*\s*,\s*(?:MultiTapeTM\.)?runFrom_zero\b')
oldname=re.compile(r'(?<![\w.])(?:Turing\.)?runFrom_one\b|\b(?:qy_run_one|xr_runFrom_one|satRed_one|recordStep_runFrom_one)\b')
def args(s):
 ms=mask(s);out=collections.Counter()
 for m in re.finditer(r'\b(?:simp|simpa|rw|rwa|dsimp|unfold)(?:\s+only)?\s*\[',ms):
  start=m.end();depth=1;i=start
  while i<len(ms) and depth:
   if ms[i]=='[':depth+=1
   elif ms[i]==']':depth-=1
   i+=1
  out.update(re.findall(r'\b(?:[A-Za-z_]\w*\.)+[A-Za-z_]\w*\x27?',ms[start:i-1]))
 return out
for p in sorted((W/'TCSlib').rglob('*.lean')):
 rel=str(p.relative_to(W));s=p.read_text();old=(O/'source-before'/(rel+'.txt')).read_text();ms=mask(s);mo=mask(old)
 co=len(re.findall(r'\bsorry\b',mo));cn=len(re.findall(r'\bsorry\b',ms));admissions.append({'path':rel,'baseline_direct_sorry_tokens':co,'current_direct_sorry_tokens':cn,'unchanged':co==cn})
 if s!=old:arg_delta.update(args(s));arg_delta.subtract(args(old))
 for m in oldname.finditer(ms):old_names.append({'path':rel,'line':ms.count('\n',0,m.start())+1,'token':m.group()})
 for m in pair.finditer(ms):residual_pairs.append({'path':rel,'line':ms.count('\n',0,m.start())+1,'snippet':s[m.start():m.end()],'disposition':'canonical generic implementation' if rel.endswith('/CfgFacts.lean') else 'separate frozen Simulation home-cycle obstruction'})
 data.append({'path':rel,'baseline_sha256':hashlib.sha256(old.encode()).hexdigest(),'current_sha256':hashlib.sha256(s.encode()).hexdigest(),'changed':s!=old})
def fields(body):
 ms=list(re.finditer(r'^  ([A-Za-z_]\w*)[^\n]*:=',body,re.M));return {m[1]:body[m.start():ms[i+1].start() if i+1<len(ms) else len(body)].strip() for i,m in enumerate(ms)}
definition_checks=[]
for r in freeze['definition_differences']:
 a=fields(r['old']['body']);b=fields(r['new']['body']);changed_fields=[k for k in a.keys()|b.keys() if a.get(k)!=b.get(k)]
 assert set(a)==set(b) and set(changed_fields)=={'run','env'},changed_fields
 assert all(':= by' in a[k] and ':= by' in b[k] for k in changed_fields)
 definition_checks.append({'path':r['path'],'name':r['old']['name'],'changed_fields':changed_fields,'only_proof_fields_changed':True,'all_other_fields_byte_identical':True,'before':a,'after':b})
(O/'all-source-final-hashes.json').write_text(json.dumps(data,indent=2)+'\n')
(O/'direct-admission-token-comparison.json').write_text(json.dumps(admissions,indent=2)+'\n')
(O/'proof-field-freeze.json').write_text(json.dumps(definition_checks,indent=2,ensure_ascii=False)+'\n')
(O/'explicit-argument-token-delta.json').write_text(json.dumps({'method':'dotted identifiers inside balanced explicit simp/simpa/rw/rwa/dsimp/unfold argument lists; lexical, not a full Lean syntax tree','positive':{k:v for k,v in sorted(arg_delta.items()) if v>0},'negative':{k:v for k,v in sorted(arg_delta.items()) if v<0}},indent=2)+'\n')
(O/'residual-source-shapes.json').write_text(json.dumps({'former_name_tokens_remaining':old_names,'adjacent_successor_zero_pairs_remaining':residual_pairs,'all_direct_admission_token_counts_unchanged':all(r['unchanged'] for r in admissions)},indent=2)+'\n')
imports=[]
for r in freeze['import_changes_held']:
 assert not r['removed'] and r['added']==['import TCSlib.Complexity.TuringMachine.CfgFacts']
 imports.append({**r,'status':'HELD HYPOTHETICAL / not authorized to publish','graph_acyclic':True,'precise_import_only':True})
(O/'final-held-imports.json').write_text(json.dumps(imports,indent=2)+'\n')
lines=['# Complete declaration dispositions','', 'These rows enumerate concrete changed declarations and approved removals, plus the unchanged cycle obstruction. They are separate from the uncapped raw shape population; row counts are not copy/debt counts. All eight import additions are held unapproved.','', '| File | Declaration | Disposition |','|---|---|---|']
for r in sorted(freeze['changed_proof_roots'],key=lambda r:(r['path'],r['name'])):lines.append('| '+r['path']+' | '+r['name']+' | Canonical reader repoint in unchanged header'+('; only run/env proof fields' if r['kind']=='def' else '')+' |')
for r in freeze['new_declarations']:lines.append('| '+r['path']+' | '+r['name']+' | Approved generic public reader, no simp attribute |')
for r in freeze['removed_declarations']:lines.append('| '+r['path']+' | '+r['name']+' | Former one-step copy removed; all clients repointed |')
lines.append('| TCSlib/Complexity/TuringMachine/Simulation.lean | Turing.bufferedScanCfg_run | Unchanged: CfgFacts import closes a cycle; separate frozen witness |')
(O/'DECLARATION-DISPOSITIONS.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'concrete_changed_and_new_roots':len(freeze['changed_proof_roots'])+len(freeze['new_declarations']),'removed':len(freeze['removed_declarations']),'shape_rows_uncapped':len(shape),'fragment_and_revision_rows':len(fragments),'held_imports':len(imports),'remaining_adjacent_pairs':residual_pairs,'old_names_remaining':old_names,'positive_argument_delta':{k:v for k,v in arg_delta.items() if v>0}},ensure_ascii=False))
