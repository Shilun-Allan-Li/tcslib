"""Prepare inert proof-only candidate and instrumentation; never touch the actual source."""
from pathlib import Path
import sys,re,json,hashlib,difflib,ast,importlib.util
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4]
s=(out/'before-Primitives.lean.txt').read_text();helper=(out/'helper-v1.lean.txt').read_text()
insert=s.rfind('/--',0,s.index('private lemma fwdMap_backB'))
c=s[:insert]+helper+'\n'+s[insert:]
for side,flag,other,sketch in [('B','true','(a.length - 1)',"**Proof sketch.** Specialize the shared buffer-rewind induction to the second buffer. The\ninactive first-buffer head stays at `|a|-1`, and the final blank transition enters its rewind\nphase with the second-buffer head restored to zero."),('A','false','0',"**Proof sketch.** Specialize the shared buffer-rewind induction to the first buffer. The\ninactive second-buffer head stays at zero, and the final blank transition enters emission\nwith both buffer heads at zero.")]:
    start=c.index('private lemma fwdMap_back'+side);body=c.index(':= by\n',start)+len(':= by\n');end=c.index('\n/--',body)
    c=c[:body]+'  simpa only [Bool.false_eq_true, ↓reduceIte] using\n    fwdMap_back '+flag+' M x a b p '+other+'\n'+c[end:]
    docstart=c.rfind('/--',0,start);docbody=c.index('**Proof sketch.**',docstart);docend=c.index(' -/',docbody)
    c=c[:docbody]+sketch+c[docend:]
(out/'candidate-Primitives.lean.txt').write_text(c)
patch=''.join(difflib.unified_diff(s.splitlines(keepends=True),c.splitlines(keepends=True),fromfile='a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean',tofile='b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean'))
(out/'proposed-factoring.patch').write_text(patch)
# Trusted local parser: only extract the pure balanced-header function from the old maintainer script.
spec=importlib.util.spec_from_file_location('parser',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
tree=ast.parse((root/'campaign/fills/mig1/landing/review-final-source/source_review.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='split_header');ns={'P':P,'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),'trusted-balanced-header-function','exec'),ns);split_header=ns['split_header']
P.header=lambda t:P.norm(split_header(t)[0])
def decls(t):
    rows=[]
    for d in P.decls(t):
        raw=d['raw'];m=re.search(r'(?m)^/(?:--|-!)',raw)
        if m:raw=raw[:m.start()]
        h,delimiter,body=split_header(raw.rstrip()+'\n');rows.append(dict(d,raw=raw.rstrip()+'\n',header_raw=h,body=body,body_code=P.norm(P.clean(body))))
    return rows
old,new=decls(s),decls(c);a={d['name']:d for d in old};b={d['name']:d for d in new};common=set(a)&set(b)
assert set(b)-set(a)=={'Turing.FinTM.fwdMap_back'} and not set(a)-set(b)
assert [d['name'] for d in old]==[d['name'] for d in new if d['name'] in a]
assert all(a[n]['header_raw']==b[n]['header_raw'] and a[n]['private']==b[n]['private'] and a[n]['kind']==b[n]['kind'] for n in common)
changes=[n for n in common if a[n]['body_code']!=b[n]['body_code']];assert set(changes)=={'Turing.FinTM.fwdMap_backA','Turing.FinTM.fwdMap_backB'}
assert all(a[n]['raw']==b[n]['raw'] for n in common if a[n]['kind'] not in ['lemma','theorem'])
assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',P.clean(helper))
imports=lambda t:[l for l in P.clean(t).splitlines() if l.startswith('import ')];assert imports(s)==imports(c)
freeze={'old_declarations':len(a),'candidate_declarations':len(b),'old_public_headers':sum(not d['private'] for d in old),'surviving_literal_headers_visibility_kind_equal':True,'surviving_relative_order_equal':True,'all_definition_inductive_instance_chunks_byte_identical':True,'all_old_proofs_other_than_backA_backB_byte_identical':all(a[n]['raw']==b[n]['raw'] for n in common if n not in changes),'imports_equal':True,'added':[{'name':'Turing.FinTM.fwdMap_back','private':True,'kind':'lemma'}],'removed':[],'changed_proof_bodies':sorted(changes),'actual_source_sha256':hashlib.sha256(s.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(c.encode()).hexdigest(),'candidate_bytes':len(c.encode()),'candidate_lines':len(c.splitlines()),'candidate_root_ranges':[{'name':n,'line':b[n]['start'],'end':b[n]['start']+len(b[n]['raw'].splitlines())-1} for n in ['Turing.FinTM.fwdMap_back','Turing.FinTM.fwdMap_backB','Turing.FinTM.fwdMap_backA']]}
(out/'freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
metadata='''
namespace Turing.FinTM
#print axioms fwdMap_back
#print axioms fwdMap_backB
#print axioms fwdMap_backA
end Turing.FinTM
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let wanted := ["fwdMap_back", "fwdMap_backB", "fwdMap_backA"]
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    match n with
    | .str _ base => if wanted.contains base then roots := roots.push n
    | _ => pure ()
  if roots.size != 3 then throwError "Expected exactly three roots, found {roots.size}"
  let simpSet ← liftTermElabM getSimpTheorems
  for r in roots do
    logInfo m!"ROOT|{r}|private={isPrivateName r}|simp={simpSet.isLemma (.decl r)}|unfold={simpSet.toUnfold.contains r}"
  for (n, ci) in env.constants.toList do
    if !roots.any (fun r => r.isPrefixOf n) then continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"AXIOMS|{n}|{(axs.qsort Name.lt).toList}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut seen : Array Name := #[]
    for x in used do
      if seen.contains x then continue
      seen := seen.push x
      match env.getModuleIdxFor? x, env.find? x with
      | some idx, some (.defnInfo di) =>
        let owner := env.header.moduleNames[idx.toNat]!
        if (`TCSlib).isPrefixOf owner then
          let hint := match di.hints with
            | .abbrev => "abbrev" | .opaque => "opaque" | .regular _ => "regular"
          logInfo m!"DEF|{n}|{x}|{owner}|hint={hint}"
      | _, _ => pure ()
'''
(out/'Candidate-native-v1.lean.txt').write_text(c+metadata)
# Each proof region gets its own local strong-seal scope. Native consumers remain otherwise exact.
manifest=json.loads((root/'campaign/fills/mig1/landing/review-primitives/Final-sections-sealed-v2-manifest.json').read_text());defs=manifest['definitions'];suppress='attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
wrapper='section\nattribute [local irreducible] '+' '.join(defs)+'\n'+suppress
sealed=c
for n in ['Turing.FinTM.fwdMap_backA','Turing.FinTM.fwdMap_backB','Turing.FinTM.fwdMap_back']:
    row=b[n];raw=row['raw'];assert sealed.count(raw)==1;sealed=sealed.replace(raw,wrapper+raw+'end\n',1)
restored=sealed
for n in ['Turing.FinTM.fwdMap_backA','Turing.FinTM.fwdMap_backB','Turing.FinTM.fwdMap_back']:
    raw=b[n]['raw'];assert restored.count(wrapper+raw+'end\n')==1;restored=restored.replace(wrapper+raw+'end\n',raw,1)
assert restored==c
(out/'Candidate-sealed-v1.lean.txt').write_text(sealed+metadata)
(out/'seal-manifest.json').write_text(json.dumps({'definitions':defs,'sections':3,'suppressed_default_definition_simp':['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],'restores_exact_candidate':True,'claim':'Only the new common helper and two repointed consumers; unchanged same-home helper proofs are consumed opaquely, no new legacy whole-module seal claim.','reuse_control_template':'../review-primitives/Controls-37-unsealed-v1.lean.txt; final37 effective pointwise/abstracted pairs, will freshly execute in this complete context.'},indent=2)+'\n')
print(json.dumps(freeze,indent=2));print('Created complete native/sealed inert copies; actual source untouched.')
