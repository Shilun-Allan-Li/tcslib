from pathlib import Path
import json,re,hashlib
O=Path(__file__).parent;P=O/'project';maps=json.loads((O/'DRAFT-SOURCE-MAP.json').read_text());guards=['Turing.MultiTapeTM.runFrom','Turing.MultiTapeTM.step'];rows=[]
for path in sorted({m['path'] for m in maps}):
 label=Path(path).stem;text=(P/path).read_text();selected=[m for m in maps if m['path']==path]
 for m in selected:
  chunk=(O/m['new_chunk']).read_text();tail=''
  if chunk.endswith('\nend Turing\n'):chunk=chunk[:-len('end Turing\n')];tail='end Turing\n'
  assert text.count(chunk)==1,(path,m['name'])
  index=text.index(chunk);doc='';before=text[:index].rstrip()
  if before.endswith('-/'):
    dstart=before.rfind('/--')
    assert dstart>=0,(path,m['name'],'missing preceding declaration docstring')
    doc=text[dstart:index]
  complete=doc+chunk
  assert text.count(complete)==1,(path,m['name'],'complete declaration chunk')
  sec='FE1Seal_'+re.sub(r'[^A-Za-z0-9_]','_',m['name'])
  enveloped='section '+sec+'\nattribute [local irreducible] '+' '.join(guards)+'\n'+complete+'end '+sec+'\n'
  text=text.replace(complete,enveloped)
 f=P/('FE1Sealed_'+label+'.lean');f.write_text(text);(O/'seals').mkdir(exist_ok=True);(O/'seals'/(f.name+'.txt')).write_text(text)
 # Recover the exact full draft source by removing only declared envelopes.
 recovered=text
 for m in selected:
  sec='FE1Seal_'+re.sub(r'[^A-Za-z0-9_]','_',m['name']);prefix='section '+sec+'\nattribute [local irreducible] '+' '.join(guards)+'\n';suffix='end '+sec+'\n';assert recovered.count(prefix)==1 and recovered.count(suffix)==1;recovered=recovered.replace(prefix,'').replace(suffix,'')
 assert recovered==(P/path).read_text()
 rows.append({'label':label,'path':path,'sealed_file':str(f.relative_to(O)),'sealed_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'targets':[m['name'] for m in selected],'guards':guards,'roundtrip_exact':True,'guard_before_complete_docstring_header_body':True,'scope':'Complete target declaration chunks under2 ordinary API guards. Explicit read audit covers changed hunks; unchanged operational legacy portions are not globally reapproved.'})
 imports='\n'.join(ln for ln in (P/path).read_text().splitlines() if ln.startswith('import '))+'\n'
 common=imports+'''set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Turing
variable {k : ℕ} {Symbol State : Type} {input : List Symbol}
variable (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) (n : ℕ)
'''
 controls=f'''theorem FE1_{label}_run_point : tm.runFrom cfg n = tm.step^[n] cfg := by rfl
#check FE1_{label}_run_point
theorem FE1_{label}_run_abstract :
    (tm.runFrom : Cfg k Symbol State input → ℕ → Cfg k Symbol State input) =
      fun cfg n => tm.step^[n] cfg := by rfl
#check FE1_{label}_run_abstract
theorem FE1_{label}_step_point : tm.step cfg =
    (match cfg.state with
      | none => cfg
      | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg) := by rfl
#check FE1_{label}_step_point
theorem FE1_{label}_step_abstract :
    (tm.step : Cfg k Symbol State input → Cfg k Symbol State input) =
      fun cfg => match cfg.state with
        | none => cfg
        | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg := by rfl
#check FE1_{label}_step_abstract
'''
 for side in ['native','sealed']:
  attr='' if side=='native' else 'attribute [local irreducible] '+' '.join(guards)+'\n'
  data=common+attr+controls;cf=P/(f'FE1Controls_{label}_{side}.lean');cf.write_text(data);(O/'seals'/(cf.name+'.txt')).write_text(data)
(O/'SEAL-SOURCE-MAP.json').write_text(json.dumps(rows,indent=2)+'\n');print('sealed target scopes',sum(len(d['targets']) for d in rows),'contexts',len(rows),'paired controls',4*len(rows))
