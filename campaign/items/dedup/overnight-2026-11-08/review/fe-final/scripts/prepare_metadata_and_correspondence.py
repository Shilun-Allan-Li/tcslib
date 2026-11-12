from pathlib import Path
import json,hashlib,re,shutil,subprocess,os
O=Path('/private/tmp/ab34-fe-live1-final-validation');E=O/'evidence';F=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4');OLD=Path('/private/tmp/ab34-overnight-fe1/EXPORT');S=Path(os.environ['TCSLIB_SCRATCH'])
def sha(b):return hashlib.sha256(b).hexdigest()
def put(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
def stripcomments(s):
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2;out.append(' ' if depth==0 else '')
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif quoted:
   out.append(s[i])
   if s[i]=='\\' and i+1<len(s):i+=1;out.append(s[i])
   elif s[i]=='"':quoted=False
   i+=1
  elif s.startswith('/-',i):depth=1;i+=2;out.append(' ')
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:
   out.append(s[i]);quoted=s[i]=='"';i+=1
 assert depth==0 and not quoted
 return ''.join(out)
def tokens(s):return re.findall(r'"(?:\\.|[^"\\])*"|[\w\u0080-\uffff]+(?:\'[\w\u0080-\uffff]*)*|[^\s]',stripcomments(s))
paths=[r['path'] for r in json.loads((E/'SOURCE.json').read_text())['files']];maps=json.loads((OLD/'DRAFT-SOURCE-MAP.json').read_text());sealmap=json.loads((OLD/'SEAL-SOURCE-MAP.json').read_text());rows=[]
for p in paths:
 b=(F/p).read_bytes();text=b.decode();body=(OLD/'draft-source'/(p+'.txt')).read_bytes();final=OLD/'sketch-source'/(p+'.txt');fb=final.read_bytes() if final.exists() else body
 assert b==fb,(p,'root final source not exact original final candidate')
 assert tokens(text)==tokens(body.decode()),(p,'tokens differ from executed body')
 sm=next(r for r in sealmap if r['path']==p);sealedfile=OLD/'seals'/('FE1Sealed_'+sm['label']+'.lean.txt');sealed=sealedfile.read_text();recovered=sealed
 for name in sm['targets']:
  sec='FE1Seal_'+re.sub(r'[^A-Za-z0-9_]','_',name);prefix='section '+sec+'\nattribute [local irreducible] '+' '.join(sm['guards'])+'\n';suffix='end '+sec+'\n';assert recovered.count(prefix)==1 and recovered.count(suffix)==1;recovered=recovered.replace(prefix,'').replace(suffix,'')
 assert recovered.encode()==body
 targets=[]
 for m in [m for m in maps if m['path']==p]:
  old=(OLD/m['old_chunk']).read_text();new=(OLD/m['new_chunk']).read_text();assert old.split(':=',1)[0]==new.split(':=',1)[0]
  header=new.split(':=',1)[0];assert text.count(header)==1,(p,m['name'],'header not exactonce')
  targets.append({'name':m['name'],'full_old_new_header_exact':True,'header':header,'header_sha256':sha(header.encode()),'old_chunk_file':m['old_chunk'],'new_chunk_file':m['new_chunk'],'old_chunk_sha256':sha(old.encode()),'new_chunk_sha256':sha(new.encode())})
 rows.append({'path':p,'final_sha256':sha(b),'prior_executed_body_sha256':sha(body),'exact_final_candidate_bytes':True,'comment_stripped_code_tokens_equal_to_prior_native_and_sealed':True,'code_tokens_sha256':sha(json.dumps(tokens(text),ensure_ascii=False).encode()),'old_sealed_input_sha256':sha(sealedfile.read_bytes()),'prior_seal_envelope_recovery_literal_body_exact':True,'bounded_guard_names':sm['guards'],'bounded_guard_applications':len(sm['targets'])*len(sm['guards']),'targets':targets})
for name in ['REVIEW.md','MANIFEST.json','SHA256SUMS','NATIVE-RESULTS.json','SEAL-RESULTS.json','CONTROL-VERIFICATION.json','READER-RESULTS.json','SEAL-SOURCE-MAP.json','DRAFT-SOURCE-MAP.json','EXPLICIT-ARGUMENT-REVIEW.json','SKETCH-SYNC.json','SOURCE-FREEZE.json']:
 d=E/'prior-bounded-evidence'/name;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(OLD/name,d)
for name in ['seals','sealed-runs','reader-probes','reader-runs','native','draft-chunks','blocks','draft-source','sketch-source']:
 shutil.copytree(OLD/name,E/'prior-bounded-evidence'/name,dirs_exist_ok=True)
put(E/'CODE-CORRESPONDENCE.json',{'PASS':True,'owners':5,'target_declarations':11,'rows':rows,'new_seal_execution':False,'literal_prior_seal_recovery':True,'paired_controls':26,'scope_limit':'Prior actual complete-declaration runFrom/step guards cover11 target chunks (22 applications) only; three-definition terminal-action reader is separate. This does not seal the full foreign-definition closure of inherited operational portions or certify global opacity. Final sketch bytes receive their own actual complete replay compilation.'})
baseobjs=json.loads((E/'baseline-adoption/object-hashes.json').read_text());actual=json.loads((E/'INPUT-895-before.json').read_text());assert {r['path']:r['sha256'] for r in actual}==baseobjs
leantree=json.loads((E/'baseline-adoption/Lean-tree.json').read_text());bt=json.loads((E/'BASE-whole-Lean-tree.json').read_text());assert {r['path']:r['blob'] for r in bt}==leantree
put(E/'BASELINE-LINEAGE-CHECK.json',{'PASS':True,'all895_actual_input_hashes_equal_published_MAC8_adoption':True,'all1003_BASE_Lean_paths_and_blobs_equal_published9b5_adoption':True,'adoption_is_historical_not_new_elaboration':True})
order=(E/'replay-order.txt').read_text().splitlines();sources=[]
for m in order:
 p=m+'.lean';b=(F/p).read_bytes();d=E/'replay-source'/(p+'.txt');d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b);sources.append({'path':p,'bytes':len(b),'sha256':sha(b)})
put(E/'REPLAY-SOURCE-MAP.json',sources)
P=O/'live/metadata-project';(P/'.lake').mkdir(parents=True,exist_ok=True);link=P/'.lake/packages'
if not link.exists():link.symlink_to(F/'.lake/packages',target_is_directory=True)
shutil.copyfile(F/'lean-toolchain',P/'lean-toolchain')
owners=[p[:-5].replace('/','.') for p in paths]
probe='\n'.join('import '+m for m in owners)+'''\n\n/- Read-only compiled declaration metadata and dependency-axiom census. No proof values are rendered. -/\nset_option maxHeartbeats 0\nset_option pp.universes true\nset_option pp.width 200\nopen Lean Elab Command Meta in\nrun_cmd do\n  let env ← getEnv\n  let owners : List Name := ['''+', '.join('`'+m for m in owners)+''']\n  for home in owners do\n    unless (env.getModuleIdx? home).isSome do throwError "missing owned import {home}"\n  let st ← liftTermElabM getSimpTheorems\n  let kind := fun (ci : ConstantInfo) => match ci with\n    | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"\n    | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"\n    | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"\n  let entries := env.constants.toList.filterMap fun (n, ci) =>\n    match env.getModuleIdxFor? n with\n    | some i =>\n      let home := env.header.moduleNames[i.toNat]!\n      if owners.contains home then some (n, ci, home) else none\n    | none => none\n  for (n, ci, home) in entries.toArray.qsort (fun a b => a.1.toString < b.1.toString) do\n    let hints := match ci with\n      | .defnInfo di => match di.hints with\n        | .abbrev => "abbrev" | .opaque => "opaque" | .regular h => s!"regular:{h}"\n      | _ => "not_definition"\n    let ip ← liftCoreM <| getInstancePriority? n\n    let typePretty ← liftTermElabM <| Meta.ppExpr ci.type\n    let axs ← liftCoreM <| Lean.collectAxioms n\n    let row := Json.mkObj [\n      ("name", toJson n.toString), ("owner", toJson home.toString),\n      ("kind", toJson (kind ci)), ("private", toJson (isPrivateName n)),\n      ("internal", toJson n.isInternalDetail), ("levelParams", toJson (ci.levelParams.map Name.toString)),\n      ("typeExpr", toJson (reprStr ci.type)), ("typePretty", toJson typePretty.pretty),\n      ("valuePresent", toJson ci.value?.isSome), ("unsafe", toJson ci.isUnsafe),\n      ("partial", toJson ci.isPartial), ("kernelHints", toJson hints),\n      ("reducibility", toJson (reprStr (getReducibilityStatusCore env n))),\n      ("simp", toJson (st.isLemma (.decl n))), ("unfold", toJson (st.toUnfold.contains n)),\n      ("protected", toJson (isProtected env n)), ("instancePriority", toJson ip),\n      ("axioms", toJson ((axs.qsort Name.lt).toList.map Name.toString))]\n    logInfo m!"META|{row.compress}"\n  logInfo m!"COMPLETE|{entries.length}|owners=5"\n'''
(P/'Inventory.lean').write_text(probe);(E/'Inventory.lean.txt').write_text(probe)
print(json.dumps({'correspondence':'PASS5owners11roots22guard-applications26paired-identities','baseline_lineage':'PASS895/1003','replay_source_files':len(order),'metadata_probe':str(P/'Inventory.lean')}))
