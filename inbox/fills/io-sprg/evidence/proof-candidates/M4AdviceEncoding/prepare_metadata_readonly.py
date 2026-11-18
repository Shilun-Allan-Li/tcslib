from pathlib import Path
import json,csv,io,re,hashlib
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B=Path('/private/tmp/io-sprg-proof-notes/M4AdviceEncoding')
area='TCSlib/Cryptography/Obfuscation/StructuredSeed/'
API={
area+'Basic.lean':'encodeList_injective_of_fixedWidth encodeList_length_of_fixedWidth',
area+'Encoding.lean':"encBuckets_injective encDraw_injective encIdx'_length_le pubLen_le_seedBound ell_le_ellBound n_le_nBound m_le_mBound encOneDraw_eq encDraw_eq encIdx'_eq",
area+'Params.lean':'kappaOf_le kappaOfN_le pubLen_eq',
area+'Defs.lean':'PrimeParam.enc_eq',
area+'BoolPRG.lean':'challengeStr_eq',
'TCSlib/Cryptography/LWE/Encoding.lean':'encodeChallenge_injective',
'TCSlib/Cryptography/Encoding/Modular.lean':'encodeVector_injective encodeMatrix_injective encodeVector_length encodeMatrix_length',
'TCSlib/Complexity/TuringMachine/Encoding.lean':'pairEncode_injective length_pairEncode',
'TCSlib/Cryptography/Candidates/Arithmetic.lean':'natToList_injOn length_natToList',
'TCSlib/Complexity/Randomized/PolyExpr.lean':'eval_mono eval_const eval_var eval_add eval_mul eval_pow',
area+'Reductions/LPN.lean':'lpnEnc_eq encLPNAdvice_eq lpnAdviceBound_eq lpnAdviceProductEquiv_apply',
area+'Reductions/PRG.lean':'prgEnc_eq encPRGAdvice_eq prgAdviceBound_eq prgAdviceDataBound_eq prodEquiv_eq'}
rows=[];binding={}
for filename,names in API.items():
 p=W/filename;s=p.read_text();binding[filename]=hashlib.sha256(p.read_bytes()).hexdigest()
 for name in names.split():
  hits=[(n,l) for n,l in enumerate(s.splitlines(),1) if re.search(r'\b(?:theorem|lemma|def|abbrev) '+re.escape(name)+r'(?=\s|\()',l)]
  assert hits,(filename,name)
  for n,line in hits:rows.append({'name':name,'source_anchor':filename+':'+str(n),'declaration_line':line.strip(),'use':'PUBLIC_REUSE_OR_OWNER_READER','source_sha256':binding[filename]})
stream=io.StringIO();out=csv.DictWriter(stream,fieldnames=list(rows[0]),delimiter='\t',lineterminator='\n');out.writeheader();out.writerows(rows);(B/'APIs.tsv').write_text(stream.getvalue())
roots=['TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN','TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG']
seen=set();todo=roots[:]
while todo:
 mod=todo.pop()
 if mod in seen:continue
 seen.add(mod);p=W/(mod.replace('.','/')+'.lean')
 if not p.exists():continue
 for l in p.read_text().splitlines():
  m=re.match(r'^import\s+(TCSlib\.[\w.]+)',l)
  if m and m.group(1) not in seen:todo.append(m.group(1))
probe_modules=['TCSlib.Cryptography.Encoding.Modular','TCSlib.Complexity.CircuitComplexity.Uniform','TCSlib.Complexity.TuringMachine.Encoding','TCSlib.Cryptography.LWE.Encoding','TCSlib.Cryptography.Obfuscation.StructuredSeed.Basic']
assert all(m in seen for m in probe_modules)
(B/'source-bindings.json').write_text(json.dumps({'scope':'READ_ONLY_SOURCE_SNAPSHOT_NOT_GIT_OR_KERNEL_STATUS','source_sha256':binding,'template_TCSlib_roots_already_in_reduction_closure':probe_modules,'closure_method':'Static local TCSlib import edges from both reduction owners. LibrarySearch is probe harness only; no source import change.'},indent=2)+'\n')
originals=['lpnEnc_injective','encLPNAdvice_injective','encLPNAdvice_length_le','prgEnc_injective','encPRGAdvice_injective','encPRGAdvice_length_le']
index=[]
for p in sorted((B/'overlap/templates').glob('*.template')):
 stem=p.name.removesuffix('.lean.template');idx=int(stem[:2])
 index.append({'id':stem,'template':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'scope':'EXPLICIT_M1_BASIC_REUSE_CONTROL' if idx>=7 else 'PUBLIC_ONLY_EXPANDED_ORIGINAL_CORE','original':originals[idx-1] if idx<=6 else 'encodeList_injective_of_fixedWidth' if idx==7 else 'encodeList_length_of_fixedWidth','exact_status':'NOT_RUN','apply_status':'NOT_RUN','owned_reduction_imports':False,'whole_goal_assumptions':False})
(B/'overlap/probe-index.json').write_text(json.dumps(index,indent=2)+'\n')
print(len(rows),'API anchors; all five probe TCSlib roots already loaded; eight NOT_RUN templates.')
