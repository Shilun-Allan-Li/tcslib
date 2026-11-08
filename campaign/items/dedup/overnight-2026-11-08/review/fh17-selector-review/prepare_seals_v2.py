from pathlib import Path
import json,re,hashlib,shutil
O=Path(__file__).parent
T=json.loads((O/'TASK.json').read_text())
W=Path(T['source_worktree'])
P=O/'live/project-v2'
(P/'.lake').mkdir(parents=True,exist_ok=True)
link=P/'.lake/packages'
if not link.exists():
    link.symlink_to(W/'.lake/packages',target_is_directory=True)
shutil.copyfile(W/'lean-toolchain',P/'lean-toolchain')
D=O/'seals-v2'
D.mkdir(exist_ok=True)
rows=[]

def last_comment_start(s):
    i=len(s)-2
    depth=0
    while i>=0:
        if s[i:i+2]=='-/':
            depth+=1
            i-=2
        elif s[i:i+2]=='/-':
            depth-=1
            if depth==0:
                return i
            i-=2
        else:
            i-=1
    raise AssertionError('unbalanced preceding block comment')

for index,path in enumerate(sorted({r['path'] for r in T['todo']}),1):
    label=str(index)+'_'+Path(path).stem
    guards=['Turing.MultiTapeTM.runFrom','Turing.MultiTapeTM.step']
    if Path(path).stem=='Clean':
        guards.append('Turing.MultiTapeTM.initCfg')
    source=(W/path).read_text()
    text=source
    selected=[r for r in T['todo'] if r['path']==path]
    envelopes=[]
    scope_rows=[]
    for r in selected:
        chunk=(O/'new-chunks'/(str(r['id'])+'.lean.txt')).read_text()
        lines=chunk.splitlines(keepends=True)
        stop=len(lines)
        for j,line in enumerate(lines[1:],1):
            if re.match(r'^(?:end|namespace|section|open|variable|include|omit|attribute|set_option)\b',line):
                stop=j
                break
        while stop and not lines[stop-1].strip():
            stop-=1
        body=''.join(lines[:stop])
        assert text.count(body)==1,(path,r['name'])
        at=text.index(body)
        start=at
        before=text[:at].rstrip()
        if before.endswith('-/'):
            start=last_comment_start(before)
        while True:
            m=re.search(r'(?m)^open [^\n]+ in[ \t]*\n[ \t\n]*\Z',text[:start])
            if m is None:
                break
            start=m.start()
        complete=text[start:at]+body
        assert text.count(complete)==1
        sec='FH1Seal_'+str(r['id'])
        prefix='section '+sec+'\nattribute [local irreducible] '+' '.join(guards)+'\n'
        suffix='end '+sec+'\n'
        text=text.replace(complete,prefix+complete+suffix)
        envelopes.append((prefix,suffix))
        scope_rows.append({'id':r['id'],'complete_scoped_open_docstring_header_body':True,'excludes_following_namespace_transitions':True,'complete_source_sha256':hashlib.sha256(complete.encode()).hexdigest()})
    recovered=text
    for a,b in envelopes:
        assert recovered.count(a)==recovered.count(b)==1
        recovered=recovered.replace(a,'').replace(b,'')
    assert recovered==source
    def add(kind,data,identities=None):
        name='FH1Sealed_'+label if kind=='full_target_scopes' else 'FH1Controls_'+label+'_'+kind.split('_')[-1]
        f=P/(name+'.lean')
        f.write_text(data)
        evidence=D/(name+'.lean.txt')
        evidence.write_text(data)
        row={'label':label,'path':path,'kind':kind,'input':str(f),'input_evidence':str(evidence.relative_to(O)),'input_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'guards':guards}
        if identities is not None:
            row['identities']=identities
        else:
            row.update({'targets':[r['id'] for r in selected],'guard_applications':len(guards)*len(selected),'literal_roundtrip_final_source_exact':True,'scopes':scope_rows})
        rows.append(row)
    add('full_target_scopes',text)
    imports='\n'.join(l for l in source.splitlines() if l.startswith('import '))+'\n'
    common=imports+'''set_option maxHeartbeats 0
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
    identities=4
    if Path(path).stem=='Clean':
        identities=6
        controls+=f'''theorem FH1_{label}_init_point : tm.initCfg input = Cfg.init tm.q₀ input := by rfl
#check FH1_{label}_init_point
theorem FH1_{label}_init_abstract :
    (tm.initCfg : (input : List Symbol) → Cfg k Symbol State input) =
      fun input => Cfg.init tm.q₀ input := by rfl
#check FH1_{label}_init_abstract
'''
    add('controls_native',common+controls,identities)
    add('controls_sealed',common+'attribute [local irreducible] '+' '.join(guards)+'\n'+controls,identities)
(O/'SEAL-INPUTS-v2.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Prepared exact scopes13/guards27, with46 paired identities; Clean additionally guards initCfg')
