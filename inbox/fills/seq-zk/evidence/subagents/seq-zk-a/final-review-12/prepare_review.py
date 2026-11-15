from pathlib import Path
import json,re,collections,hashlib,importlib.util,sys
sys.dont_write_bytecode=True
ROOT=Path('/Users/seyoonr/.codex/worktrees/seq-zk-proof/tcslib-exchange')
OUT=Path(__file__).resolve().parent
DIR=ROOT/'evidence/rule10/final-repair/explicit'
scan=json.loads((DIR/'explicit-final.json').read_text())
original=json.loads((DIR/'explicit-items.json').read_text())['items']
touched=json.loads((DIR/'touched.json').read_text())
spec=importlib.util.spec_from_file_location('seq_zk_readonly_lexer',ROOT/'evidence/tools/rule10/archived-gate10-tools/scan_explicit.py')
lex=importlib.util.module_from_spec(spec);spec.loader.exec_module(lex)
sources={f:(ROOT/f).read_text() for f in touched['files']}
codes={f:lex.blank(s).splitlines() for f,s in sources.items()}
lines={f:s.splitlines() for f,s in sources.items()}
P='TCSlib.Cryptography.'
aliases={
 'mul_zero':('PUBLIC_PROOF_VALUED_CLASS_FIELD_ALIAS',['MulZeroClass.mul_zero'],'Mathlib.Algebra.GroupWithZero.Defs:35–37,77 exports the class equality fields; simp uses their proposition, not a definition equation.'),
 'zero_mul':('PUBLIC_PROOF_VALUED_CLASS_FIELD_ALIAS',['MulZeroClass.zero_mul'],'Mathlib.Algebra.GroupWithZero.Defs:35–37,77 exports the class equality fields; simp uses their proposition, not a definition equation.'),
 'not_not':('PUBLIC_THEOREM_EXPORT_ALIAS',['Classical.not_not'],'Mathlib.Logic.Basic:188 exports Classical.not_not, declared in Init.Classical:141.'),
 'hpV.trans':('LOCAL_PROOF_METHOD',['Eq.trans'],'hpV is a local congrArg equality at SequentialZK.lean:669; .trans combines it with local hp.'),
 'List.mem_singleton.mp':('PUBLIC_THEOREM_IFF_ELIMINATION',['List.mem_singleton','Iff.mp'],'The source applies the mp direction of the public singleton-membership iff to local hm.'),
 'List.prefix_iff_eq_append.mp':('PUBLIC_THEOREM_IFF_ELIMINATION',['List.prefix_iff_eq_append','Iff.mp'],'The source applies the mp direction of the public prefix-characterization iff to local hp.'),
 'hA.advice_eq':('PUBLIC_THEOREM_METHOD_ALIAS',['Complexity.NUPPT.Uniform.advice_eq'],'hA is an obtained Uniform witness; Randomized/PPT.lean:300 publishes this exact equality reader.'),
 'hS.advice_eq':('PUBLIC_THEOREM_METHOD_ALIAS',['Complexity.NUPPT.Uniform.advice_eq'],'hS is a Uniform hypothesis; Randomized/PPT.lean:300 publishes this exact equality reader.'),
 'h.realCoinsEquiv_fst_ofFn':('PUBLIC_THEOREM_METHOD_ALIAS',[P+'SequentialZK.PaddedProverSpec.realCoinsEquiv_fst_ofFn'],'EndpointSampling.lean:166 publishes the theorem in PaddedProverSpec; h is its specification receiver.'),
 'd.phase_take':('PUBLIC_THEOREM_METHOD_ALIAS',[P+'Composability.PaddedVerifierSpec.phase_take'],'RepeatedVerifier.lean:170 publishes phase_take with explicit specification receiver d.'),
 'd.outV_eq':('PUBLIC_THEOREM_METHOD_ALIAS',[P+'Composability.PaddedVerifierSpec.outV_eq'],'RepeatedSoundness.lean:125 publishes outV_eq with explicit specification receiver d.'),
 'h.first':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'SequentialZK.PaddedProverSpec.first'],'h is a PaddedProverSpec and first is its published equality field. The argument h.first is a proof, not the projection definition itself.'),
 'h.rounds_eval':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'SequentialZK.PaddedProverSpec.rounds_eval'],'h is a PaddedProverSpec and rounds_eval is its published equality field.'),
 'd.next':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'SequentialZK.PaddedProverSpec.next'],'d is a PaddedProverSpec and next is its published reply-equation proof field.'),
 'd.boundary':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'SequentialZK.PaddedProverSpec.boundary'],'d is a PaddedProverSpec and boundary is its published history-count proof field.'),
 'd.rounds_eq':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'Composability.PaddedVerifierSpec.rounds_eq'],'d is a PaddedVerifierSpec and rounds_eq is its published equality proof field.'),
 'd.first_eq':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'Composability.PaddedVerifierSpec.first_eq'],'d is a PaddedVerifierSpec and first_eq is its published equality proof field.'),
 'd.next_eq':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'Composability.PaddedVerifierSpec.next_eq'],'d is a PaddedVerifierSpec and next_eq is its published reply-equation proof field.'),
 'd.terminal_eq':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'Composability.PaddedVerifierSpec.terminal_eq'],'d is a PaddedVerifierSpec and terminal_eq is its published verdict-equation proof field.'),
 'd.period':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'Composability.PaddedVerifierSpec.period'],'d is a PaddedVerifierSpec and period is its published mover-period proof field.'),
 'd.local_length':('PUBLIC_PROOF_VALUED_SPEC_FIELD',[P+'Composability.PaddedVerifierSpec.local_length'],'d is a PaddedVerifierSpec and local_length is its published local received-count proof field.'),
 'attempt':('OWNED_DEFINITION_OPEN_IN_ALIAS',[P+'AbortRetry.attempt'],'Defs.lean:588 has open AbortRetry in immediately before the theorem docstring. attempt is defined in this same module at328; inherited explicit use at636.'),
 'retry':('OWNED_DEFINITION_OPEN_IN_ALIAS',[P+'AbortRetry.retry'],'Defs.lean:588 has open AbortRetry in before the theorem docstring. retry is defined in this same module at346; inherited explicit use at648.'),
 'firstHit_map_getD_eq':('PUBLIC_THEOREM_OPEN_IN_ALIAS',[P+'AbortRetry.firstHit_map_getD_eq'],'Defs.lean:588 opens AbortRetry for PerfectZKAbort.statZK; the public theorem is at460 in this same module.'),
}
review=[];unlocated=[]
for idx,r in enumerate(scan['items']):
 if r['classification']!='LOCAL_OR_UNRESOLVED':continue
 f=r['file'];line=r['line'];head=r['head'];item=dict(r);item['scan_index']=idx
 ds=[d for d in touched['files'][f]['declarations'] if d['start']<=line<=d['end']]
 assert len(ds)==1,(f,line,ds)
 decl=ds[0];item['source_context']='\n'.join(f'{i+1}: {lines[f][i]}' for i in range(max(0,line-5),min(len(lines[f]),line+2)))
 if head in aliases:
  cls,targets,basis=aliases[head];item.update(review_classification=cls,native_targets=targets,review_basis=basis)
 elif head=='show':
  item.update(review_classification='INLINE_TYPED_PROOF_TERM',native_targets=[],review_basis='The scanner retained the keyword show as if it were a declaration head; the full rewrite item is an explicit typed equality proof term.')
 else:
  esc=re.escape(head)
  tok=re.compile(r'(?<![\w\u0027])'+esc+r'(?![\w\u0027])')
  matches=[]
  for i in range(decl['decl_line']-1,min(line,len(codes[f]))):
   s=codes[f][i]
   if not tok.search(s):continue
   binding=(re.search(r'\b(?:have|let|letI|set|obtain|rcases|rintro|intro|by_cases|rename_i|induction|cases|fun)\b',s)
     or re.search(r'^\s*\|',s) or re.search(r'(?<![\w\u0027])'+esc+r'\s*:',s)
     or (i<decl['decl_line']+8 and '(' in s))
   if binding:matches.append({'line':i+1,'source':lines[f][i]})
  if matches:
   item.update(review_classification='LOCAL_BINDER_PROOF_OR_LET',native_targets=[],review_basis='The enclosing compiled declaration binds this exact spelling before the scanned use; nearest source-local binding candidates retained.',binding_candidates=matches[-4:])
  else:
   item.update(review_classification='NEEDS_MANUAL_BINDING_LOCATION',native_targets=[],review_basis='No simple same-line binder pattern was found; inspect retained enclosing source.',enclosing_source='\n'.join(f'{i+1}: {lines[f][i]}' for i in range(decl['decl_line']-1,min(line+1,len(lines[f])))))
   unlocated.append(item)
 review.append(item)
targets=sorted({t for r in review for t in r['native_targets']})
result={'proof_revision':touched['head'],'raw_scan_summary':scan['summary'],'reviewed_items':len(review),'by_class':dict(collections.Counter(r['review_classification'] for r in review)),'secondary_native_targets':targets,'unlocated_items':len(unlocated),'review':review,'source_sha256':{f:hashlib.sha256(s.encode()).hexdigest() for f,s in sources.items()}}
(OUT/'proposed-resolutions.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
(OUT/'secondary-native-targets.json').write_text(json.dumps({'targets':targets,'requirement':'Print native kind, projection status, home and type-is-Prop. Proof-valued fields legitimately have kind def; do not require all targets theorem-kind. No Lean execution by this subagent.'},indent=2)+'\n')
(OUT/'unlocated-binding-contexts.json').write_text(json.dumps(unlocated,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['review','source_sha256']},indent=2))
