from pathlib import Path
import json,gzip,hashlib
P=Path('/private/tmp/mig-post234-final-head-accounting');ctx=json.loads((P/'context.json').read_text());B=Path(ctx['baseline_frozen_folder']);auth=json.loads((P/'metadata-summary.json').read_text())['public_authored_shared_type_changes'];types={}
for line in gzip.open(B/'Base.out.gz','rt'):
 if line.startswith('CENSUS|'):
  r=json.loads(line.split('|',1)[1])
  if r['name']in auth:types[r['name']]=r['typeExpr']
assert set(types)==set(auth)and len(types)==5
matchers=[json.loads(l.split('|',1)[1])for l in gzip.open(P/'Base-type-matchers-v2.out.gz','rt')if l.startswith('ORDINARY_MATCHER|')];assert len(matchers)==3
current=['Turing.FinTM.computesFunInTime_pairConcat_spaceUsed.match_1','Turing.FinTM.computesFunInTime_splitSolve_spaceUsed.match_1','Turing.FinTM.computesFunInTime_stripLast_spaceUsed.match_1'];imports=''.join('import '+m+'\n'for m in ctx['primary_owners']+ctx['context_owners'])+'import Lean\n';
def safe_name_literals(expr):
 out=[];i=0
 while i<len(expr):
  if expr[i]=='"':
   _,n=json.JSONDecoder().raw_decode(expr[i:]);out.append(expr[i:i+n]);i+=n;continue
  if expr[i]!='`':out.append(expr[i]);i+=1;continue
  i+=1;start=i;quoted=0
  while i<len(expr):
   ch=expr[i]
   if ch=='«':quoted+=1
   elif ch=='»':quoted-=1
   elif not quoted and(ch.isspace()or ch in '()[],'):break
   i+=1
  raw=expr[start:i];parts=[];part=[];quoted=0
  for ch in raw:
   if ch=='«':quoted+=1
   elif ch=='»':quoted-=1
   elif ch=='.'and not quoted:parts.append(''.join(part));part=[]
   else:part.append(ch)
  parts.append(''.join(part));name='Lean.Name.anonymous'
  for part in parts:name='(Lean.Name.mkStr '+name+' '+json.dumps(part,ensure_ascii=False)+')'
  out.append(name)
 return ''.join(out)

probe=imports+'''/-! Bounded cross-context type comparison. Reconstruct exactly three safe ordinary BASE
matcher definitions, then kernel-check their defining equality to HEAD matchers and equality
of the five complete BASE/HEAD public type expressions. No theorem value is read/rendered;
no unsafe/transparency override is used. This is a metadata probe, not a source edit. -/
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open Lean Elab Command Meta in
run_cmd do
'''
for r in matchers:
 assert r['safety']=='Lean.DefinitionSafety.safe'and r['hintsExpr']=='Lean.ReducibilityHints.abbrev'
 probe+='  do\n    let oldName : Name := '+safe_name_literals(r['nameExpr'])+'\n    unless !(← getEnv).contains oldName do throwError "old matcher already present {oldName}"\n    let oldType : Expr := '+safe_name_literals(r['typeExpr'])+'\n    let oldValue : Expr := '+safe_name_literals(r['valueExpr'])+'\n    unless reprStr oldType == '+json.dumps(r['typeExpr'],ensure_ascii=False)+' do throwError "BASE matcher type literal mismatch"\n    unless reprStr oldValue == '+json.dumps(r['valueExpr'],ensure_ascii=False)+' do throwError "BASE ordinary matcher value literal mismatch"\n    liftCoreM <| addDecl (.defnDecl { name := oldName, levelParams := '+safe_name_literals(r['levelParamsExpr'])+', type := oldType, value := oldValue, hints := .abbrev, safety := .safe })\n    logInfo m!"BASE_ORDINARY_MATCHER_RECONSTRUCTED|{oldName}|kernelChecked=true"\n'
probe+='''  let checkEquality := fun (label : String) (levelParams : List Name) (left right : Expr) => do
    let (goalType, proof) ← liftTermElabM do
      let goalType ← mkEq left right
      let goal ← mkFreshExprSyntheticOpaqueMVar goalType
      goal.mvarId!.refl
      pure (← instantiateMVars goalType, ← instantiateMVars goal)
    let kernelName := Name.mkSimple ("MIGCurrentTypeEquality_" ++ label)
    liftCoreM <| addDecl (.thmDecl { name := kernelName, levelParams := levelParams, type := goalType, value := proof })
    logInfo m!"TYPE_EQUALITY|{label}|PASS|kernelChecked={kernelName}"
'''
for i,(r,n)in enumerate(zip(matchers,current),1):
 probe+='  do\n    let oldName : Name := '+safe_name_literals(r['nameExpr'])+'\n    let newName : Name := `'+n+'\n    let oldInfo ← getConstInfo oldName\n    let newInfo ← getConstInfo newName\n    unless oldInfo.levelParams.length == newInfo.levelParams.length do throwError "matcher level parameter arity mismatch"\n    let levels := newInfo.levelParams.map Level.param\n    checkEquality "matcher_'+str(i)+'" newInfo.levelParams (mkConst oldName levels) (mkConst newName levels)\n'
for i,n in enumerate(auth,1):
 probe+='  do\n    let baselineType : Expr := '+safe_name_literals(types[n])+'\n    unless reprStr baselineType == '+json.dumps(types[n],ensure_ascii=False)+' do throwError "BASE public type literal mismatch '+n+'"\n    let currentInfo ← getConstInfo `'+n+'\n    checkEquality "public_'+str(i)+'" currentInfo.levelParams baselineType currentInfo.type\n    logInfo "PUBLIC_TYPE_IDENTITY|'+n+'|BASE_literal_exact=true|HEAD_actual_type=true|kernel_rfl=true"\n'
probe+='  logInfo "TYPE_TRANSPORT_COMPLETE|ordinaryMatchers=3|publicTypes=5|no_theorem_values_rendered"\n'
assert 'withTransparency'not in probe and 'isDefEq'not in probe and '.thmInfo'not in probe and 'ci.value'not in probe
(P/'TypeTransport-HeadKernel-v2.lean.txt').write_text(probe);project=Path(ctx['project']);(project/'TypeTransport-HeadKernel-v2.lean').write_text(probe);(P/'type-transport-head-job.json').write_text(json.dumps([{'name':'Head-type-transport-kernel-v2','side':'Head','project_file':'TypeTransport-HeadKernel-v2.lean','evidence_file':'TypeTransport-HeadKernel-v2.lean.txt'}],indent=2)+'\n');(P/'type-transport-input-identities.json').write_text(json.dumps({'base':ctx['base'],'head':ctx['source'],'ordinary_matcher_transport':[{'base_name':r['name'],'head_name':n,'base_type_sha256':hashlib.sha256(r['typeExpr'].encode()).hexdigest(),'base_ordinary_value_sha256':hashlib.sha256(r['valueExpr'].encode()).hexdigest(),'only_safe_ordinary_definitions':True}for r,n in zip(matchers,current)],'public_types':[{'name':n,'base_type_utf8_bytes':len(types[n].encode()),'base_type_sha256':hashlib.sha256(types[n].encode()).hexdigest()}for n in auth],'probe_sha256':hashlib.sha256(probe.encode()).hexdigest(),'no_theorem_proof_values_read_or_rendered':True,'no_unsafe_or_transparency_override':True,'all_8_equalities_must_be_kernel_checked':True},indent=2)+'\n');print('HEAD probe',len(probe.encode()),hashlib.sha256(probe.encode()).hexdigest())
