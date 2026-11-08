"""Prepare a single inert proof-body repoint and its one-region strong seal."""
from pathlib import Path
import json,hashlib,difflib,sys,importlib.util,ast,re
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4];before=(out/'before-Primitives.lean.txt').read_text();name='Turing.FinTM.fwdMapVirtual_run';start=before.index('private lemma fwdMapVirtual_run ');body=before.index(':= by\n',start)+len(':= by\n');end=before.index('\n/--',body);docstart=before.rfind('/--',0,start);docend=before.index('-/',docstart)+2
newdoc='''/-- Payload forwarding preserves its entire source trajectory at all times,
including the final halting action and the stationary halted tail.

**Proof sketch.** Use `fwdMapVirtual_step` to show that times with a matching encoded source
configuration and valid arrival tag are closed under successor. The general invariant iterator
propagates the initial correspondence to every time. -/'''
candidate=before[:docstart]+newdoc+before[docend:body]+(out/'body-v1.lean.txt').read_text()+before[end:];(out/'candidate-Primitives.lean.txt').write_text(candidate)
(out/'proposed-repoint.patch').write_text(''.join(difflib.unified_diff(before.splitlines(keepends=True),candidate.splitlines(keepends=True),fromfile='a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean',tofile='b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean')))
spec=importlib.util.spec_from_file_location('P',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
tree=ast.parse((root/'campaign/fills/mig1/landing/review-final-source/source_review.py').read_text());fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='split_header');ns={'P':P,'re':re};exec(compile(ast.Module(body=[fn],type_ignores=[]),'trusted-full-header','exec'),ns);split=ns['split_header']
def decls(text):
 rows=[]
 for d in P.decls(text):
  raw=d['raw'];m=re.search(r'(?m)^/(?:--|-!)',raw)
  if m:raw=raw[:m.start()]
  h,delimiter,b=split(raw.rstrip()+'\n');rows.append(dict(d,raw=raw.rstrip()+'\n',header_raw=h,body=b,body_code=P.norm(P.clean(b))))
 return rows
old,new=decls(before),decls(candidate);a={d['name']:d for d in old};b={d['name']:d for d in new};assert set(a)==set(b);assert [d['name'] for d in old]==[d['name'] for d in new];assert all(a[n]['header_raw']==b[n]['header_raw'] and a[n]['private']==b[n]['private'] and a[n]['kind']==b[n]['kind'] for n in a);assert [n for n in a if a[n]['body_code']!=b[n]['body_code']]==[name];assert all(a[n]['raw']==b[n]['raw'] for n in a if n!=name)
newstart=candidate.index('private lemma fwdMapVirtual_run ');newdocstart=candidate.rfind('/--',0,newstart);newend=candidate.index('\n/--',newstart);assert before[:docstart]==candidate[:newdocstart] and before[end:]==candidate[newend:];assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',P.clean(b[name]['body']))
metadata='''
namespace Turing.FinTM
#print axioms fwdMapVirtual_run
end Turing.FinTM
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    match n with
    | .str _ "fwdMapVirtual_run" => roots := roots.push n
    | _ => pure ()
  if roots.size != 1 then throwError "Expected exactly one root, found {roots.size}"
  let st ← liftTermElabM getSimpTheorems
  for r in roots do
    logInfo m!"ROOT|{r}|private={isPrivateName r}|simp={st.isLemma (.decl r)}|unfold={st.toUnfold.contains r}"
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
(out/'Candidate-native-v1.lean.txt').write_text(candidate+metadata)
manifest=json.loads((out.parent/'review-forward-rewind-factoring/seal-v2-manifest.json').read_text());defs=manifest['definitions'];w='section\nattribute [local irreducible] '+' '.join(defs)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n';region=candidate[newdocstart:newend];sealed=candidate[:newdocstart]+w+region+'\nend\n'+candidate[newend:];assert sealed.replace(w+region+'\nend\n',region,1)==candidate
(out/'Candidate-sealed-v1.lean.txt').write_text(sealed+metadata)
H=lambda s:hashlib.sha256(s.encode()).hexdigest()
(out/'freeze.json').write_text(json.dumps({'before_sha256':H(before),'candidate_sha256':H(candidate),'before_declarations':len(old),'candidate_declarations':len(new),'public_headers':sum(not d['private'] for d in old),'all_literal_full_headers_visibility_kinds_order_equal':True,'all_other_declaration_chunks_byte_equal':True,'entire_source_outside_target_doc_and_proof_byte_equal':True,'imports_attributes_runtime_type_data_unchanged':True,'added':[],'removed':[],'changed_proof':name,'new_leading_proof_sketch':True,'candidate_bytes':len(candidate.encode()),'candidate_lines':len(candidate.splitlines())},indent=2)+'\n')
(out/'seal-manifest.json').write_text(json.dumps({'sections':1,'definitions':defs,'default_definition_simps_removed':['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'],'doc_and_header_inside_guard':True,'exact_wrapper_removal_restores_candidate':True,'scope':'Only fwdMapVirtual_run; same-home step theorem and unchanged helper proofs are consumed opaquely.'},indent=2)+'\n');print((out/'freeze.json').read_text())
