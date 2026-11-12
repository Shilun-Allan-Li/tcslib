from pathlib import Path
import ast,re,sys,json,hashlib,subprocess,datetime,time,difflib
B=Path(__file__).resolve().parents[1];cfg=json.loads((B/'qa/config.json').read_text());O=B/'source-freeze';O.mkdir();(O/'chunks').mkdir()
helper=B/'tools/declfreeze.py';tree=ast.parse(helper.read_text());allowedAssign={'KW','DECL','ANON','STOP','SCOPE'}
nodes=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))or isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in allowedAssign for t in n.targets)]
ns={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),ns);chunks=ns['chunks'];stmt=ns['stmt']
authorized={'TCSlib/Complexity/ClassNP/EXP.lean':['Complexity.enumCont_first_anchor'],'TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean':['Turing.xr_firstArrival',"Turing.xr_firstArrival'"],'TCSlib/Complexity/CookLevin/Hardness.lean':['Complexity.clBank_first','Complexity.clCopy_first','Complexity.clRow_first','Complexity.clCmp_first','Complexity.clFirst'],'TCSlib/Complexity/TuringMachine/Build/InputCall.lean':['Turing.inputSeekRewind_run']}
def digest(x):return hashlib.sha256(x.encode()).hexdigest()
def mask(s):
 out=list(s);depth=0;i=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;out[i]=out[i+1]=' ';i+=2;continue
  if depth and s.startswith('-/',i):depth-=1;out[i]=out[i+1]=' ';i+=2;continue
  if depth:
   if s[i]!='\n':out[i]=' '
   i+=1;continue
  if s.startswith('--',i):
   j=s.find('\n',i);j=len(s)if j<0 else j
   for k in range(i,j):out[k]=' '
   i=j;continue
  i+=1
 return ''.join(out)
def indexed(s):
 rows=[];cursor=0
 for n,private,text in chunks(s):
  start=s.find(text,cursor);assert start>=cursor,(n,start,cursor);end=start+len(text);cursor=end
  rows.append({'name':n,'private':private,'text':text,'start':start,'end':end,'line':s.count('\n',0,start)+1})
 return {r['name']:r for r in rows}
sourceRows=[];receipts=[];targetRows=[];phaseData={}
for path,names in authorized.items():
 a=(Path(cfg['BASE_export'])/path).read_text();b=(Path(cfg['HEAD_export'])/path).read_text();A=indexed(a);D=indexed(b);assert A.keys()==D.keys()
 changed=[n for n in A if A[n]['text']!=D[n]['text']];assert set(changed)==set(names),(path,changed,names)
 assert all(A[n]['private']==D[n]['private']for n in A)
 assert all(A[n]['private']and D[n]['private']for n in names)
 assert all(A[n]['text']==D[n]['text']for n in A if n not in names)
 restored=b
 for n in sorted(names,key=lambda n:D[n]['start'],reverse=True):restored=restored[:D[n]['start']]+A[n]['text']+restored[D[n]['end']:]
 assert restored==a,path
 importsA=re.findall(r'^import[^\n]*',a,re.M);importsB=re.findall(r'^import[^\n]*',b,re.M);assert importsA==importsB
 stem=Path(path).stem
 cmd=[sys.executable,'-I',str(helper),str(Path(cfg['BASE_export'])/path),str(Path(cfg['HEAD_export'])/path),','.join(n.rsplit('.',1)[-1]for n in names)]
 start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();run=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 (O/(stem+'-declfreeze.out')).write_bytes(run.stdout);(O/(stem+'-declfreeze.err')).write_bytes(run.stderr)
 rec={'path':path,'command':cmd,'cwd':str(Path.cwd()),'start_utc':start,'seconds':time.monotonic()-t,'exit':run.returncode,'stdout_SHA256':hashlib.sha256(run.stdout).hexdigest(),'stderr_SHA256':hashlib.sha256(run.stderr).hexdigest(),'helper_SHA256':hashlib.sha256(helper.read_bytes()).hexdigest(),'scope':'Canonical parser output plus separately asserted full byte recovery/header checks; CLI exit alone is not a semantic freeze verdict'};receipts.append(rec);(O/(stem+'-declfreeze-receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');assert run.returncode==0
 for n in names:
  aa=A[n];bb=D[n];parts={}
  for phase,r in [('BASE',aa),('HEAD',bb)]:
   text=r['text'];masked=mask(text);decl=re.search(r'^(?:private\s+)(?:theorem|lemma)\s+',masked,re.M);assert decl,n
   delim=re.search(r':=\s*by\b',masked[decl.start():]);assert delim,n;stop=decl.start()+delim.start();header=text[decl.start():stop]
   f=O/'chunks'/(phase+'-'+n.replace("'",'_prime')+'.lean.txt');f.write_text(text+'\n');parts[phase]={'full_chunk_capture':str(f.relative_to(B)),'full_chunk_SHA256':digest(text),'source_start_offset':r['start'],'source_end_offset':r['end'],'source_start_line':r['line'],'literal_header':header,'literal_header_SHA256':digest(header),'private':r['private']}
  assert parts['BASE']['literal_header']==parts['HEAD']['literal_header'],n
  targetRows.append({'path':path,'name':n,'BASE':parts['BASE'],'HEAD':parts['HEAD'],'literal_header_exact':True,'parser_statement_exact':stmt(aa['text'])==stmt(bb['text'])})
 sourceRows.append({'path':path,'BASE_SHA256':digest(a),'HEAD_SHA256':digest(b),'BASE_bytes':len(a.encode()),'HEAD_bytes':len(b.encode()),'BASE_splitlines':len(a.splitlines()),'HEAD_splitlines':len(b.splitlines()),'BASE_style_newline_count':len(a.split('\n')),'HEAD_style_newline_count':len(b.split('\n')),'changed_full_chunks':names,'all_names_privacy_exact':True,'public_chunk_bodies_and_headers_exact':True,'all_non_target_chunks_exact':True,'imports_exact':True,'reversing_exact_nine_authorized_chunks_recovers_all_other_BASE_bytes':True,'parser_public_count':sum(not r['private']for r in A.values()),'parser_private_count':sum(r['private']for r in A.values())})
 phaseData[path]=(a,b,A,D)
assert len(targetRows)==9
hp='TCSlib/Complexity/CookLevin/Hardness.lean';a,b,A,D=phaseData[hp];hold='Complexity.clA5Compare_compute';assert A[hold]['text']==D[hold]['text']
(O/'held-comparator-BASE-HEAD-identical.lean.txt').write_text(A[hold]['text']+'\n')
il='TCSlib/Complexity/TuringMachine/Build/InputLength.lean';ia=(Path(cfg['BASE_export'])/il).read_bytes();ib=(Path(cfg['HEAD_export'])/il).read_bytes();assert ia==ib
result={'BASE':cfg['source_base'],'HEAD':cfg['source_head'],'current_owner_count':4,'authorized_private_target_count':9,'targets':targetRows,'files':sourceRows,'canonical_parser_cli_receipts':receipts,'literal_headers_exact_for_all9':True,'public_authored_source_changes':False,'runtime_definition_or_import_changes':False,'full_source_recovery_exact':True,'held_comparator_full_chunk_including_sketch_exact_BASE':True,'held_InputLength_whole_source_exact_BASE':True,'held_InputLength_SHA256':hashlib.sha256(ia).hexdigest(),'limitations':'Declfreeze is lexical; exact whole-source reversal plus literal9-header checks and the independent compiled50 ABI comparison provide the stronger bounds. No full type equality is claimed for omitted private/generated declarations.'}
(O/'SOURCE-FREEZE.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'owners':4,'private_changed_chunks':9,'headers_exact':True,'source_recovery_exact':True,'runtime_import_public_source_changes':False,'held2_BASE_exact':True,'declfreeze_CLI_exits':[r['exit']for r in receipts]}))
