from pathlib import Path
import json,re,hashlib,shutil
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());W=Path(pin['source_worktree']);OLD=Path('/private/tmp/ab34-first-halt-reuse-remaining/EXPORT');F=json.loads((O/'FOOTPRINT-SUMMARY.json').read_text());rows=[]

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
  else:out.append(s[i]);quoted=s[i]=='"';i+=1
 assert depth==0 and not quoted
 return ''.join(out)

def last_comment_start(s):
 i=len(s)-2;depth=0
 while i>=0:
  if s[i:i+2]=='-/':depth+=1;i-=2
  elif s[i:i+2]=='/-':
   depth-=1
   if depth==0:return i
   i-=2
  else:i-=1
 raise AssertionError('unbalanced preceding comment')

for original in pin['roots']:
 idx=original['id'];path=original['path'];foot=next(r for r in F['rows'] if r['id']==idx);source=(O/'source'/(path+'.txt')).read_text();chunk=(OLD/original['final_complete_chunk']).read_text();assert source.count(chunk)==1
 lines=chunk.splitlines(keepends=True);stop=len(lines)
 for j,line in enumerate(lines[1:],1):
  if re.match(r'^(?:end|namespace|section|open|variable|include|omit|attribute|set_option)\b',line):stop=j;break
 while stop and not lines[stop-1].strip():stop-=1
 body=''.join(lines[:stop]);assert source.count(body)==1;at=source.index(body);start=at;before=source[:at].rstrip()
 if before.endswith('-/'):start=last_comment_start(before)
 while True:
  m=re.search(r'(?m)^open [^\n]+ in[ \t]*\n[ \t\n]*\Z',source[:start])
  if m is None:break
  start=m.start()
 end=at+len(body);prefix=source[:end];stack=[]
 for line in stripcomments(prefix).splitlines():
  m=re.fullmatch(r'\s*(namespace|section|noncomputable section)(?:\s+([^\s]+))?\s*',line)
  if m:stack.append({'kind':m.group(1),'name':m.group(2) or ''});continue
  m=re.fullmatch(r'\s*end(?:\s+([^\s]+))?\s*',line)
  if m:
   assert stack,(idx,'unmatched end',line)
   stack.pop()
 heads=foot['ordinary_head_names'];info={r['name']:r for r in json.loads((O/'ORDINARY-UNION.json').read_text())};simpnames=[n for n in heads if info[n]['simp'] or info[n]['unfold']];sec='FHFullBoundary_'+str(idx)
 attr='section '+sec+'\nattribute [local irreducible] '+' '.join(heads)+'\n'
 if simpnames:attr+='attribute [-simp] '+' '.join(simpnames)+'\n'
 code=source[:start]+attr+source[start:end]
 guard_check='''\nopen Lean Elab Command Meta in
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
  logInfo m!"GUARD_OK|''' +str(idx)+'''|{(Json.arr states.reverse.toArray).compress}"
'''
 code+=guard_check+'end '+sec+'\n'
 code+=''.join('end'+(' '+r['name'] if r['name'] else '')+'\n' for r in reversed(stack))
 P=O/'live/guard-projects'/('root-'+str(idx));(P/'.lake').mkdir(parents=True,exist_ok=True);(P/'.lake/packages').symlink_to(W/'.lake/packages',target_is_directory=True);shutil.copyfile(W/'lean-toolchain',P/'lean-toolchain');f=P/path;f.parent.mkdir(parents=True,exist_ok=True);f.write_text(code);d=O/'guard-inputs'/(str(idx)+'-'+original['name'].replace('.','_')+'.lean.txt');d.parent.mkdir(exist_ok=True);d.write_text(code)
 plain=source[:end]+''.join('end'+(' '+r['name'] if r['name'] else '')+'\n' for r in reversed(stack));pd=O/'original-prefixes'/(str(idx)+'-'+original['name'].replace('.','_')+'.lean.txt');pd.parent.mkdir(exist_ok=True);pd.write_text(plain)
 assert code[:start]==source[:start]
 rows.append({'id':idx,'name':original['name'],'path':path,'root':foot['root'],'project':str(P),'input':str(f),'input_evidence':str(d.relative_to(O)),'input_sha256':hashlib.sha256(code.encode()).hexdigest(),'source_HEAD':pin['HEAD'],'full_source_sha256':hashlib.sha256(source.encode()).hexdigest(),'prefix_through_complete_target_end':end,'exact_complete_target_doc_header_body_start':start,'ordinary_heads':heads,'ordinary_head_count':len(heads),'definition_simp_rows_removed':simpnames,'original_open_scopes_closed_after_target':stack,'no_proof_stubs':True,'actual_preceding_source_context_preserved':True})
(O/'GUARD-INPUTS.json').write_text(json.dumps(rows,indent=2)+'\n');print('Prepared17 full ordinary-head guard prefixes, no proof stubs')
