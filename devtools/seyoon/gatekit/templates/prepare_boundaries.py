from pathlib import Path
import ast,re,json,hashlib,shutil
O=Path(__file__).parent;W=Path(json.loads((O/'PIN.json').read_text())['source_worktree']);M=json.loads((O/'METADATA-CANDIDATE.json').read_text());h=O/'helpers/declfreeze.py';t=ast.parse(h.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(h),'exec'),ns);H=lambda b:hashlib.sha256(b).hexdigest();pin=json.loads((O/'PIN.json').read_text());headers=[];union={};rows=[]
def clean(s):
 out=[];i=0;depth=0;quote=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif quote:
   out.append(s[i])
   if s[i]=='\\' and i+1<len(s):i+=1;out.append(s[i])
   elif s[i]=='"':quote=False
   i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   e=s.find('\n',i);i=len(s) if e<0 else e
  else:out.append(s[i]);quote=s[i]=='"';i+=1
 return ''.join(out)
for idx,m in enumerate(M,1):
 path=m['owner'].replace('.','/')+'.lean';source=(O/'source/CANDIDATE'/(path+'.txt')).read_text();base=(O/'source/BASE'/(path+'.txt')).read_text();suffix=m['name'].rsplit('.',1)[-1];name,pr,c=next(x for x in ns['chunks'](source) if x[0].endswith('.'+suffix));_,bpr,bc=next(x for x in ns['chunks'](base) if x[0]==name);assert pr==bpr;cidx=c.index(':= by');bidx=bc.index(':= by');assert c[:cidx]==bc[:bidx];at=source.index(c);start=at
 while True:
  z=re.search(r'(?m)^open [^\n]+ in\s*\n\s*\Z',source[:start])
  if not z:break
  start=z.start()
 end=at+len(c);stack=[]
 for line in clean(source[:end]).splitlines():
  z=re.fullmatch(r'\s*(namespace|section|noncomputable section)(?:\s+([^\s]+))?\s*',line)
  if z:stack.append(z.group(2) or '');continue
  if re.fullmatch(r'\s*end(?:\s+([^\s]+))?\s*',line):assert stack;stack.pop()
 defs=[x for x in m['foreign_definitions'] if x['ordinary']];heads=[x['name'] for x in defs];assert heads;union.update({d['name']:d for d in defs});simp=[d['name'] for d in defs if d['simp'] or d['unfold']];sec='ReaderRepairBoundary_'+str(idx);attr='section '+sec+'\nattribute [local irreducible] '+' '.join(heads)+'\n';attr+=('attribute [-simp] '+' '.join(simp)+'\n') if simp else '';code=source[:start]+attr+source[start:end]+'''\nopen Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let st ← liftTermElabM getSimpTheorems
  let names : List Name := ['''+', '.join('`'+n for n in heads)+''']
  let mut states : List Json := []
  for n in names do
    match getReducibilityStatusCore env n with
    | .irreducible => pure ()
    | _ => throwError "GUARD_NOT_IRREDUCIBLE|{n}"
    if st.toUnfold.contains n || st.isLemma (.decl n) then
      throwError "GUARD_DEFINITION_SIMP_STILL_ACTIVE|{n}"
    states := Json.mkObj [("name",toJson n.toString),("irreducible",toJson true),
      ("definition_simp_unfold",toJson false)] :: states
  logInfo m!"GUARD_OK|'''+str(idx)+'''|{(Json.arr states.reverse.toArray).compress}"
end '''+sec+'\n'+''.join('end'+(' '+n if n else '')+'\n' for n in reversed(stack));d=O/'guards'/str(idx);d.mkdir(parents=True,exist_ok=True);(d/'source.lean.txt').write_text(code);project=O/'runtime'/('guard-'+str(idx));(project/'.lake').mkdir(parents=True,exist_ok=True);(project/'.lake/packages').symlink_to(W/'.lake/packages',target_is_directory=True);shutil.copyfile(W/'lean-toolchain',project/'lean-toolchain');q=project/path;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(code);rows.append({'id':idx,'name':name,'kernel_root':m['name'],'owner':path,'project':str(project),'source_capture':str((d/'source.lean.txt').relative_to(O)),'source_sha256':H(code.encode()),'heads':heads,'simp_removed':simp,'complete_target_start':at,'insert_start':start,'complete_target_end':end,'original_scope_closures':stack,'native_complete_chunk_sha256':H(c.encode()),'literal_doc_header_before_assignment_exact':True});headers.append({'id':idx,'name':name,'path':path,'full_literal_doc_header':c[:cidx],'BASE_chunk':bc,'CANDIDATE_chunk':c,'public':not pr})
(O/'GUARD-INPUTS.json').write_text(json.dumps(rows,indent=2)+'\n');(O/'HEADERS6.json').write_text(json.dumps(headers,indent=2)+'\n');(O/'ORDINARY-UNION.json').write_text(json.dumps(list(union.values()),indent=2)+'\n');print('Prepared',len(rows),'complete-prefix guards;',len(union),'ordinary heads:',sorted(union))
