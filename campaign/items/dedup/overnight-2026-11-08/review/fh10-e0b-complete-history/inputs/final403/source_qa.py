from pathlib import Path
import re,json,hashlib,subprocess,datetime,shutil
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());W=Path(pin['source_worktree']);P=Path('/private/tmp/ab34-first-halt-full-boundary');prior=json.loads((P/'PIN.json').read_text());OLD=Path('/private/tmp/ab34-first-halt-reuse-remaining/EXPORT');git=lambda *a:subprocess.check_output(['git','-C',str(W),*a]);assert git('rev-parse','HEAD').decode().strip()==pin['HEAD'];assert not git('status','--porcelain','--untracked-files=no');assert git('rev-parse','refs/remotes/origin/codex/ab34-first-halt-reuse').decode().strip()==pin['HEAD'];git('cat-file','-e',pin['HEAD']+'^{commit}');git('cat-file','-e',pin['BASE']+'^{commit}')
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
code=lambda s:' '.join(stripcomments(s).split());roots=[];owners=[];kept=set(pin['kept_ids']);repairs={17:'reader17',47:'reader47',54:'reader54'}
for row in pin['owners']:
 path=row['path'];base=(O/'source/BASE'/(path+'.txt')).read_text();head=(O/'source/HEAD'/(path+'.txt')).read_text();assert head==(W/path).read_text();back=head
 for r in prior['roots']:
  if r['id'] not in kept or r['path']!=path:continue
  old=(OLD/r['old_complete_chunk']).read_text();new=(P/'hypotheses'/repairs[r['id']]/'new-chunk.lean.txt').read_text() if r['id'] in repairs else (OLD/r['final_complete_chunk']).read_text();assert base.count(old)==head.count(new)==1;h=lambda x:x[:re.search(r':= by(?:\n|$)',x).start()];assert h(old)==h(new);back=back.replace(new,old,1);d=O/'root-chunks'/str(r['id']);d.mkdir(parents=True);(d/'BASE.lean.txt').write_text(old);(d/'HEAD.lean.txt').write_text(new);roots.append({'id':r['id'],'path':path,'name':r['name'],'BASE_line':base[:base.index(old)].count('\n')+1,'HEAD_line':head[:head.index(new)].count('\n')+1,'BASE_chunk_sha256':hashlib.sha256(old.encode()).hexdigest(),'HEAD_chunk_sha256':hashlib.sha256(new.encode()).hexdigest(),'literal_complete_header':h(new),'literal_complete_header_exact':True,'outer_proof_delimiter_used':':= by','HEAD_chunk':f'root-chunks/{r["id"]}/HEAD.lean.txt','BASE_chunk':f'root-chunks/{r["id"]}/BASE.lean.txt'})
 assert code(back)==code(base),(path,'non-target code drift');imports=lambda s:re.findall(r'^import\s+[^\n]+$',stripcomments(s),flags=re.M);assert imports(base)==imports(head);owners.append({'path':path,'all_non_target_code_tokens_exact':True,'all_import_lines_exact':True,'BASE_sha256':hashlib.sha256(base.encode()).hexdigest(),'HEAD_sha256':hashlib.sha256(head.encode()).hexdigest()})
assert len(roots)==10 and len(owners)==8
held=[]
for r in prior['roots']:
 if r['id'] in kept:continue
 path=r['path'];base=git('show',pin['BASE']+':'+path);head=git('show',pin['HEAD']+':'+path);assert base==head==(W/path).read_bytes();held.append({'id':r['id'],'name':r['name'],'path':path,'HEAD_entire_owner_exact_BASE':True,'sha256':hashlib.sha256(head).hexdigest()})
changed=[x for x in git('diff','--name-only',pin['BASE'],pin['HEAD'],'--','*.lean').decode().splitlines() if x];assert set(changed)=={r['path'] for r in owners};maps=[]
for rev in ['BASE','HEAD']:
 d={}
 for line in git('ls-tree','-r',pin[rev]).decode().splitlines():
  fields,path=line.split('\t',1)
  if path.endswith('.lean'):d[path]=fields.split()[2]
 maps.append(d);(O/(rev+'-ALL-LEAN-BLOBS.json')).write_text(json.dumps(d,indent=2)+'\n')
assert set(maps[0])==set(maps[1]);diff=[p for p in maps[0] if maps[0][p]!=maps[1][p]];assert set(diff)==set(changed)
context=O/'context';context.mkdir(exist_ok=True)
for p in ['devtools/seyoon/leanelab.sh','devtools/seyoon/declfreeze.py','policy.md','workflow.md','campaign/standards/TEMPLATE.md','campaign/maintainer/START-HERE.md','campaign/maintainer/WORKFLOW.md']:
 q=context/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((W/p).read_bytes())
shutil.copyfile('/private/tmp/ab34-fh10-source-adoption.json',context/'root-source-adoption.json');out=O/'declfreeze';out.mkdir();freezes=[];allowed=','.join(r['name'] for r in roots)
for row in owners:
 path=row['path'];argv=['python3','-I',str(context/'devtools/seyoon/declfreeze.py'),str(O/'source/BASE'/(path+'.txt')),str(O/'source/HEAD'/(path+'.txt')),allowed];run=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);raw=run.stdout;assert run.returncode==0 and not any(x in raw for x in [b'STATEMENT CHANGED:',b'UNAUTHORIZED BODY CHANGE:']);file=path.replace('/','__')+'.out';(out/file).write_bytes(raw);freezes.append({'path':path,'argv':argv,'exit':run.returncode,'output':'declfreeze/'+file,'output_sha256':hashlib.sha256(raw).hexdigest()})
# Exact full population sources, both endpoints, for auditor screen replay.
population=(O/'screen-population.txt').read_text().splitlines();pop=[]
for path in population:
 row={'path':path}
 for rev in ['BASE','HEAD']:
  raw=git('show',pin[rev]+':'+path);f=O/'population-source'/rev/(path+'.txt');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(raw);row[rev]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'blob':git('rev-parse',pin[rev]+':'+path).decode().strip()}
 pop.append(row)
(O/'ROOT-HEADER-FREEZE10.json').write_text(json.dumps(sorted(roots,key=lambda r:r['id']),indent=2)+'\n');(O/'SOURCE-PRESERVATION8.json').write_text(json.dumps(owners,indent=2)+'\n');(O/'HELD7-RESTORED.json').write_text(json.dumps(held,indent=2)+'\n');(O/'DECLFREEZE-RUNS.json').write_text(json.dumps(freezes,indent=2)+'\n');(O/'POPULATION-SOURCE-MAP43.json').write_text(json.dumps(pop,indent=2)+'\n');report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'HEAD':pin['HEAD'],'BASE':pin['BASE'],'actual_HEAD_tracking_clean':True,'changed_Lean_files':changed,'changed_owners':8,'root_headers_exact':10,'non_target_code_tokens_exact_all8':True,'all_import_lines_exact_all8':True,'held7_whole_owners_exact_BASE':True,'all_Lean_paths':len(maps[0]),'only_changed_Lean_blobs':8,'public_statement_change':False,'new_definition_API_import_name_home_route':False,'screen_population':len(pop),'source_screen_execution_claim':False};(O/'SOURCE-QA.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
