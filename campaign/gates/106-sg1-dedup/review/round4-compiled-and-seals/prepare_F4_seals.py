from pathlib import Path
import json,re,hashlib
P=Path('/private/tmp/g106-r4-compiled-and-seals');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');ctx=json.loads((P/'context.json').read_text());guards=(P/'F4-guard-definitions.txt').read_text().splitlines();assert len(guards)==6
chunks=json.loads((P/'F4-actual-source-chunks.json').read_text());project=Path(ctx['project']);jobs=[];identities=[];instrumentation=[]
# Generic control logic is the previously reviewed kernel-checking generator, with the
# unused recursive pairDecode special case removed. No transparency override is added.
trusted=R/'campaign/gates/106-sg1-dedup/review/round3-closure-repairs/Controls-unsealed-v1.lean.txt';s=trusted.read_text();body=s[s.index('open Lean Elab Command Meta in'):];start=body.index('  let names : List Name :=');end=body.index('  let mut index :=',start);body=body[:start]+'  let names : List Name := ['+', '.join('`'+n for n in guards)+']\n'+body[end:]
oldstart=body.index('        if n == ``Turing.pairDecode then');oldend=body.index('        else if mode == "abstract" then',oldstart);body=body[:oldstart]+'        if mode == "abstract" then'+body[oldend+len('        else if mode == "abstract" then'):]
assert 'withTransparency'not in body and 'unsafe'not in body and 'reprStr'not in body
remove='attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
guard='attribute [local irreducible] '+' '.join(guards)+'\n'
for row,label in zip(chunks,['SAT','Hardness']):
 imports=''.join('import '+n+'\n'for n in row['imports'])+'import Lean\n';chunk=(P/row['chunk']).read_text();common=imports+'set_option maxHeartbeats 0\nopen Turing\nnamespace Complexity\nsection F4Forwarder\n'+remove
 tail='\n#print axioms '+row['name']+'\nend F4Forwarder\nend Complexity\n'
 native=common+chunk+tail;sealed=common+guard+chunk+tail;assert sealed.replace(guard,'',1)==native
 for mode,source in [('native',native),('sealed',sealed)]:
  name='F4-'+label+'-'+mode;file='F4'+label+('Native'if mode=='native'else'Sealed')+'.lean';(P/(name+'.lean.txt')).write_text(source);(project/file).write_text(source);jobs.append({'name':name,'side':'Head','project_file':file,'evidence_file':name+'.lean.txt'})
 localbody=body.replace('G106ClosureRflControl_', 'G106R4'+label+'RflControl_').replace('#g106_closure_controls','#g106_r4_'+label.lower()+'_controls')
 for mode in ['native','sealed']:
  name='F4-'+label+'-controls-'+mode;file='F4'+label+'Controls'+mode.title()+'.lean';source=imports+'set_option maxHeartbeats 0\nsection F4ControlScope\n'+remove+(guard if mode=='sealed'else'')+localbody+'\nend F4ControlScope\n';(P/(name+'.lean.txt')).write_text(source);(project/file).write_text(source);jobs.append({'name':name,'side':'Head','project_file':file,'evidence_file':name+'.lean.txt','expected_exit':1 if mode=='sealed'else 0,'expected_errors':12 if mode=='sealed'else 0})
 ids=[{'definition':n,'mode':m,'kernel_name':'G106R4'+label+'RflControl_'+str(i*2+j+1)+'_'+m}for i,n in enumerate(guards)for j,m in enumerate(['point','abstract'])];identities.append({'context':label,'identities':ids})
 instrumentation.append({'context':label,'actual_source_path':row['path'],'actual_chunk':row['chunk'],'actual_chunk_sha256':hashlib.sha256(chunk.encode()).hexdigest(),'imports_exact_original_TCSlib_and_Mathlib_plus_Lean_meta':row['imports'],'guard_count':6,'default3_simps_removed_both_sides':True,'guard_before_complete_doc_header_body':True,'guard_removal_recovers_native_byte_exact':True,'positive_and_negative_identity_count_each':12,'no_unsafe_or_transparency_override':True,'only_two_actual_source_forwarders_scoped_not_legacy_global_seal':True})
(P/'F4-seal-jobs.json').write_text(json.dumps(jobs,indent=2)+'\n');(P/'F4-control-identities.json').write_text(json.dumps(identities,indent=2)+'\n');(P/'F4-instrumentation.json').write_text(json.dumps({'source':ctx['source'],'guard_union':guards,'contexts':instrumentation,'trusted_control_generator_sha256':hashlib.sha256(trusted.read_bytes()).hexdigest(),'control_adaptation':'same kernel addDecl/refl algorithm; exact6guard names; no unused pairDecode branch; context-specific names/imports'},indent=2)+'\n');print('prepared8jobs,2actualproofcontexts,6guards,12positive+12negativeeach')
