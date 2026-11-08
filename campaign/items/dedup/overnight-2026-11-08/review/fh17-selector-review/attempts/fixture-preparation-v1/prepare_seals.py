from pathlib import Path
import json,re,hashlib,shutil
O=Path(__file__).parent;T=json.loads((O/'TASK.json').read_text());W=Path(T['source_worktree']);P=O/'live/project';(P/'.lake').mkdir(parents=True,exist_ok=True);(P/'.lake/packages').symlink_to(W/'.lake/packages',target_is_directory=True);shutil.copyfile(W/'lean-toolchain',P/'lean-toolchain');rows=[];guards=['Turing.MultiTapeTM.runFrom','Turing.MultiTapeTM.step']
for index,path in enumerate(sorted({r['path'] for r in T['todo']}),1):
 label=str(index)+'_'+Path(path).stem;source=(W/path).read_text();text=source;selected=[r for r in T['todo'] if r['path']==path];envs=[]
 for r in selected:
  chunk=(O/'new-chunks'/(str(r['id'])+'.lean.txt')).read_text();body=chunk
  while re.search(r'\nend(?: [^\n]+)?\n?$',body):body=re.sub(r'\nend(?: [^\n]+)?\n?$','\n',body)
  assert text.count(body)==1,(path,r['name']);at=text.index(body);doc='';before=text[:at].rstrip()
  if before.endswith('-/'):
   d=before.rfind('/--');assert d>=0;doc=text[d:at]
  complete=doc+body;sec='FH1Seal_'+str(r['id']);prefix='section '+sec+'\nattribute [local irreducible] '+' '.join(guards)+'\n';suffix='end '+sec+'\n';assert text.count(complete)==1;text=text.replace(complete,prefix+complete+suffix);envs.append([prefix,suffix])
 recovered=text
 for a,b in envs:assert recovered.count(a)==recovered.count(b)==1;recovered=recovered.replace(a,'').replace(b,'')
 assert recovered==source
 file=P/('FH1Sealed_'+label+'.lean');file.write_text(text);d=O/'seals'/(file.name+'.txt');d.parent.mkdir(exist_ok=True);d.write_text(text);rows.append({'label':label,'path':path,'kind':'full_target_scopes','input':str(file),'input_evidence':str(d.relative_to(O)),'input_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'targets':[r['id'] for r in selected],'guards':guards,'guard_applications':2*len(selected),'complete_preceding_docstring_header_body':True,'literal_roundtrip_final_source_exact':True})
 imports='\n'.join(l for l in source.splitlines() if l.startswith('import '))+'\n';common=imports+'''set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Turing
variable {k : ℕ} {Symbol State : Type} {input : List Symbol}
variable (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) (n : ℕ)
'''
 controls=f'''theorem FH1_{label}_run_point : tm.runFrom cfg n = tm.step^[n] cfg := by rfl
#check FH1_{label}_run_point
theorem FH1_{label}_run_abstract :
    (tm.runFrom : Cfg k Symbol State input → ℕ → Cfg k Symbol State input) =
      fun cfg n => tm.step^[n] cfg := by rfl
#check FH1_{label}_run_abstract
theorem FH1_{label}_step_point : tm.step cfg =
    (match cfg.state with
      | none => cfg
      | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg) := by rfl
#check FH1_{label}_step_point
theorem FH1_{label}_step_abstract :
    (tm.step : Cfg k Symbol State input → Cfg k Symbol State input) =
      fun cfg => match cfg.state with
        | none => cfg
        | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by rfl
#check FH1_{label}_step_abstract
'''
 for side in ['native','sealed']:
  attr='' if side=='native' else 'attribute [local irreducible] '+' '.join(guards)+'\n';data=common+attr+controls;file=P/('FH1Controls_'+label+'_'+side+'.lean');file.write_text(data);d=O/'seals'/(file.name+'.txt');d.write_text(data);rows.append({'label':label,'path':path,'kind':'controls_'+side,'input':str(file),'input_evidence':str(d.relative_to(O)),'input_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'guards':guards,'identities':4})
(O/'SEAL-INPUTS.json').write_text(json.dumps(rows,indent=2)+'\n');print('Prepared11 source contexts/13 complete target scopes/26 guards/44 paired identities')
