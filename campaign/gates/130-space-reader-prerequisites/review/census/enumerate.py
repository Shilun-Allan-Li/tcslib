from pathlib import Path
import subprocess,json,hashlib,re,ast,collections,datetime,time
O=Path(__file__).parent
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
P=R/'campaign/items/dedup'
G=lambda *a: subprocess.check_output(['git','--no-optional-locks','-C',str(R),*a])
H=lambda b: hashlib.sha256(b).hexdigest()
def write(n,v): (O/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
received=Path('/private/tmp/ab34-open-prs-fetched.json')
inv=json.loads(received.read_text()); (O/'OPEN-PRS-RECEIVED.json').write_bytes(received.read_bytes())
refs0=G('for-each-ref','--format=%(refname) %(objectname)').decode()
(O/'ALL-REFS.raw.txt').write_text(refs0)
refs={l.split(' ',1)[0]:l.split(' ',1)[1] for l in refs0.splitlines()}
commit_aliases=collections.defaultdict(list);noncommit=[]
for ref,raw in refs.items():
 r=subprocess.run(['git','--no-optional-locks','-C',str(R),'rev-parse','--verify',ref+'^{commit}'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if r.returncode: noncommit.append({'ref':ref,'object':raw,'error':r.stderr.decode()});continue
 c=r.stdout.decode().strip();G('cat-file','-e',c+'^{commit}');commit_aliases[c].append(ref)
prs=[]
for row in inv['pulls']:
 ref='refs/remotes/'+row['fetched_ref'];c=G('rev-parse','--verify',ref+'^{commit}').decode().strip();G('cat-file','-e',c+'^{commit}')
 assert c==row['sha']==row['fetched_sha'],(ref,c,row)
 named='refs/remotes/origin/'+row['head'];local='refs/heads/'+row['head']
 prs.append({**row,'verified_ref':ref,'verified_source':c,'named_remote_head':refs.get(named),'named_local_head':refs.get(local),'all_ref_aliases':commit_aliases[c]})
assert len(prs)==16
write('OPEN-PRS-VERIFIED.json',prs)
records=G('rev-parse','HEAD^{commit}').decode().strip();G('cat-file','-e',records+'^{commit}')
workraw=G('worktree','list','--porcelain').decode(); (O/'WORKTREES.raw.txt').write_text(workraw)
worktrees=[]
for block in workraw.strip().split('\n\n'):
 row={}
 for line in block.splitlines():
  k,_,v=line.partition(' ');row[k]=v
 if row:worktrees.append(row)
# Every available worktree HEAD joins the commit population; unavailable directories remain disclosed.
for row in worktrees:
 c=row.get('HEAD')
 if not c:continue
 rr=subprocess.run(['git','--no-optional-locks','-C',str(R),'cat-file','-e',c+'^{commit}'],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if rr.returncode:row['head_object_unavailable']=True;continue
 commit_aliases[c].append('worktree-HEAD:'+row['worktree'])
blob_locations=collections.defaultdict(set);tree_rows=[];tree_cache={}
for c,aliases in sorted(commit_aliases.items()):
 tree=G('rev-parse',c+'^{tree}').decode().strip()
 if tree not in tree_cache:
  raw=G('ls-tree','-r','-z',tree);rows=[]
  for row in raw.split(b'\0'):
   if not row:continue
   spec,p=row.split(b'\t',1);mode,kind,oid=spec.split();p=p.decode()
   if kind==b'blob' and ((p.startswith('TCSlib/') and p.endswith('.lean')) or p=='TCSlib.lean'):rows.append((p,oid.decode()))
  tree_cache[tree]={'rows':rows,'ls_tree_sha256':H(raw),'tree_bytes':len(raw)}
 data=tree_cache[tree]
 for p,b in data['rows']:blob_locations[b].add(('ref_source',c,p))
 tree_rows.append({'commit':c,'tree':tree,'aliases':aliases,'full_ls_tree_SHA256':data['ls_tree_sha256'],'TCSlib_Lean_count':len(data['rows'])})
# Approved source proposals and other committed prepared/delivery source bytes at the current records tree.
prepared=[]
for row in G('ls-tree','-r','-z',records,'--','campaign').split(b'\0'):
 if not row:continue
 spec,p=row.split(b'\t',1);mode,kind,oid=spec.split();p=p.decode()
 if kind==b'blob' and p.endswith(('.lean','.lean.txt','.patch')):
  b=oid.decode();prepared.append({'path':p,'Git_blob':b});blob_locations[b].add(('tracked_prepared_data',records,p))
# Current changed/untracked actual Lean bytes, on all accessible registered worktrees.
working=[];workbytes={};workerrors=[]
for row in worktrees:
 w=Path(row['worktree'])
 if not w.is_dir():continue
 def gw(*a):return subprocess.check_output(['git','--no-optional-locks','-C',str(w),*a])
 try:
  changes=set(gw('diff','--name-only','HEAD','--','*.lean').decode().splitlines())
  untracked=set(gw('ls-files','--others','--exclude-standard','--','*.lean').decode().splitlines())
 except subprocess.CalledProcessError as e:workerrors.append({'worktree':str(w),'read_error':str(e)});continue
 for name in sorted(changes|untracked):
  f=w/name
  if not f.is_file() or '.lake/' in name:continue
  b=f.read_bytes();key='working-sha256:'+H(b);workbytes[key]=b;blob_locations[key].add(('working_bytes',row.get('HEAD',''),str(f)))
  working.append({'worktree':str(w),'HEAD':row.get('HEAD'),'branch':row.get('branch'),'path':name,'bytes':len(b),'sha256':H(b),'key':key,'dirty_tracked':name in changes})
write('REF-COVERAGE.json',{'started_UTC':started,'records_HEAD':records,'all_ref_count':len(refs),'commit_count':len(commit_aliases),'non_commit_refs':noncommit,'commit_source_trees':tree_rows,'all_worktree_count':len(worktrees),'available_worktree_count':sum(Path(r['worktree']).is_dir() for r in worktrees),'prepared_tracked_paths':prepared,'changed_or_untracked_actual_Lean':working,'worktree_read_errors':workerrors,'fresh_inventory_input_SHA256':H(received.read_bytes()),'scope':'All ref names returned by for-each-ref, all available registered worktree HEAD commits, every TCSlib/**/*.lean plus TCSlib.lean in their trees; current records campaign/**/*.lean/.lean.txt/.patch; changed/untracked *.lean of all available registered worktrees. Supplied 16 current open PR refs validated. No network query/fetch or semantic completeness claim by reviewer.'})
write('REF-ALIASES.json',dict(sorted(commit_aliases.items())))
helper=R/'devtools/seyoon/declfreeze.py';tree=ast.parse(helper.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re}
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(helper),'exec'),ns)
def clean(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   out.append(s[i])
   if s[i]=='\\' and i+1<len(s):i+=1;out.append(s[i])
   elif s[i]=='"':string=False
   i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(s[i]);string=s[i]=='"';i+=1
 return ''.join(out)
def header(c):
 s=clean(c);m=re.search(r'(?m)^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:def|abbrev|lemma|theorem|instance)\s+',s)
 if not m:return ''
 s=s[m.start():];depth=0;quoted=False;i=0
 while i<len(s):
  if s[i]=='"':quoted=not quoted
  if not quoted:
   if s[i] in '({[':depth+=1
   elif s[i] in ')}]':depth-=1
   elif depth==0 and s.startswith(':=',i):return s[:i]
  if quoted and s[i]=='\\':i+=1
  i+=1
 return s
names=['core_eq','bootCfg_of_halt','runCfg_initCfg','sweepRevCfg_state','sweepRevCfg_output','controlAction_eq','controlAction_def','inputMoveAction_eq','inputFoldTM_tr_bwd']
exact=re.compile(r'\b(?:'+'|'.join(map(re.escape,names))+r')\b')
term_patterns={
 'gate130_core':re.compile(r'\b(?:ConfigCount\.core|core_eq|core_iff|core_eq_iff|core_step|core_runFrom|core_injOn|coreCode_inj)\b'),
 'gate130_ND':re.compile(r'\b(?:bootCfg|runCfg|hostCfg_eq|hostCfg_init|bootCfg_of_halt|runCfg_initCfg)\b'),
 'gate130_sweep':re.compile(r'\bsweepRevCfg(?:_\w+)?\b'),
 'gate129':re.compile(r'\b(?:controlAction(?:_\w+)?|inputMoveAction(?:_\w+)?|inputFoldTM(?:_\w+)?|returnScanTM)\b')}
candidates=[];rawhits=[];manifest=[];chunk_meta={};unparsed=[];(O/'candidate-excerpts').mkdir()
ids=[b for b in blob_locations if not b.startswith('working-')]
cat=subprocess.Popen(['git','--no-optional-locks','-C',str(R),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
scanned_bytes=0
for idx,key in enumerate(list(blob_locations)):
 if key in workbytes:b=workbytes[key]
 else:
  cat.stdin.write((key+'\n').encode());cat.stdin.flush();hd=cat.stdout.readline().split();assert hd[0].decode()==key and hd[1]==b'blob',hd;n=int(hd[2]);b=cat.stdout.read(n);assert cat.stdout.read(1)==b'\n'
 scanned_bytes+=len(b);s=b.decode('utf-8');cl=clean(s);locs=sorted(blob_locations[key]);manifest.append({'source_blob_or_working_key':key,'bytes':len(b),'SHA256':H(b),'locations':locs})
 # Patch text receives separate after/before views: original line numbers remain in raw hits.
 views=[('source',s)]
 if any(p.endswith('.patch') for kind,c,p in locs):
  views=[]
  for side,keep in [('patch_after',('+',' ')),('patch_before',('-',' '))]:
   lines=[]
   for line in s.splitlines():
    if line.startswith(('+++','---','diff ','index ','@@')):lines.append('')
    elif line.startswith(keep):lines.append(line[1:])
    else:lines.append('')
   views.append((side,'\n'.join(lines)))
 linehits=[]
 for i,line in enumerate(cl.splitlines()):
  flags=[k for k,p in term_patterns.items() if p.search(line)]
  if exact.search(line):flags.append('exact_name')
  # bare local core is relevant only alongside the four-field tuple signature or ConfigCount owner.
  if re.search(r'\bcore\b',line) and any('/ConfigCount.' in p or '/MARMTime.' in p for _,_,p in locs):flags.append('local_core_owner')
  if flags:linehits.append({'line':i+1,'text':s.splitlines()[i],'flags':flags})
 if linehits:rawhits.append({'source_blob':key,'hits':linehits})
 if not linehits and not ('Action' in cl and '=' in cl and ('⟨' in cl or 'Action.mk' in cl)) and not all(x in cl for x in ['.state','.inputPos','.workTapes','.workTapePos']):continue
 for view,txt in views:
  cc=clean(txt)
  chunks=list(ns['chunks'](txt));matched=0
  for name,private,chunk in chunks:
   ch=clean(chunk);hd=header(chunk);flags=[]
   if exact.search(ch):flags.append('EXACT_NAME')
   for family,pattern in term_patterns.items():
    if pattern.search(hd):flags.append(family+'_STATEMENT')
    if pattern.search(ch):flags.append(family+'_BODY_OR_STATEMENT')
   if re.search(r'\bcore\b',hd) and ('ConfigCount' in name or all(t in hd for t in ['.state','.inputPos','.workTapes','.workTapePos'])):flags.append('CORE_TUPLE_STATEMENT_SHAPE')
   if all(t in hd for t in ['.state','.inputPos','.workTapes','.workTapePos']) and '=' in hd:flags.append('FOUR_FIELD_EQUALITY_STATEMENT_SHAPE')
   if 'Action' in hd and '=' in hd and ('⟨' in hd or 'Action.mk' in hd):flags.append('ACTION_CONSTRUCTOR_STATEMENT_SHAPE')
   if not flags:continue
   at=txt.find(chunk);assert at>=0
   h=H(chunk.encode());capture='candidate-excerpts/'+h+'.lean.txt'
   if h not in chunk_meta:
    (O/capture).write_text(chunk+'\n');chunk_meta[h]={'sha256_without_capture_LF':h,'capture':capture,'name':name,'private':private,'lines':len(chunk.splitlines()),'header':hd}
   candidates.append({'candidate':len(candidates)+1,'source_blob':key,'view':view,'name':name,'private':private,'source_line':txt[:at].count('\n')+1,'chunk_sha256_without_capture_LF':h,'flags':flags});matched+=1
  if linehits and not matched:unparsed.append({'source_blob':key,'view':view,'line_hits':len(linehits)})
cat.stdin.close();assert cat.wait()==0
write('SEARCHED-SOURCE-BLOBS.json',manifest);write('RAW-HITS.json',rawhits);write('CANDIDATES.json',candidates);write('CANDIDATE-CHUNKS.json',list(chunk_meta.values()));write('UNPARSED-HIT-SURFACES.json',unparsed)
prior=[]
for fam,prefix in [('configcount-core-proposal','CORE-READER'),('ndclock-startup-reader-proposal','ND-READERS'),('singletape-sweep-reader-proposal','SWEEP-READERS')]:
 p=P/fam/'2026-11-08';bind=[]
 for f in [p/'API-only.patch',p/'PROPOSAL.md',p/'EXISTING-READER-SEARCH.json',*(p/'git').glob('*REFS*'),*(p/'git').glob('*UNIQUE-HIT*')]:
  if f.is_file():bind.append({'path':str(f.relative_to(R)),'bytes':f.stat().st_size,'SHA256':H(f.read_bytes())})
 metadata=json.loads((p/'git'/f'{prefix}-ALL-AVAILABLE-REFS.json').read_text());raw=p/'git'/f'{prefix}-ALL-AVAILABLE-REFS.raw.txt';assert H(raw.read_bytes())==metadata['raw_sha256'];prior.append({'family':fam,'files':bind,'prior_search_metadata':metadata})
write('PRIOR-PROTOTYPE-BINDINGS.json',prior)
pre=Path('/private/tmp/ab34-gate129-preflight');pr=[]
for name in ['STATEMENT-TWIN.json','CURRENT-ALIGNMENT-BINDING.json','REF-COVERAGE.json','ENUMERATION-SUMMARY.json','THREE-READER-DISPOSITIONS.json','CANDIDATE-DISPOSITIONS162.json','REVIEW.md']:
 p=pre/name;pr.append({'path':str(p),'bytes':p.stat().st_size,'SHA256':H(p.read_bytes())})
write('PRIOR-GATE129-BINDINGS.json',pr)
# Verify reference bindings did not shift during the snapshot. All bytes already bound to exact objects.
refs1=G('for-each-ref','--format=%(refname) %(objectname)').decode();(O/'ALL-REFS.end.raw.txt').write_text(refs1)
summary={'started_UTC':started,'finished_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records_HEAD':records,'all_available_ref_names':len(refs),'unique_commit_heads_including_worktree_HEADs':len(commit_aliases),'distinct_full_tree_objects':len(tree_cache),'verified_current_open_PR_heads':len(prs),'prepared_tracked_source_paths':len(prepared),'available_worktrees':sum(Path(r['worktree']).is_dir() for r in worktrees),'changed_or_untracked_actual_Lean_files':len(working),'unique_source_blobs_or_byte_objects':len(manifest),'scanned_bytes':scanned_bytes,'raw_hit_blob_count':len(rawhits),'uncapped_raw_hit_lines':sum(len(x['hits']) for x in rawhits),'candidate_source_rows':len(candidates),'distinct_complete_candidate_chunks':len(chunk_meta),'unparsed_hit_surfaces':len(unparsed),'refs_unchanged_during_snapshot':refs0==refs1,'canonical_parser_path':str(helper),'canonical_parser_SHA256':H(helper.read_bytes()),'no_received_script_Lean_screen_lint_or_source_Git_mutation':True,'limits':'Candidate enumeration and complete-chunk source inspection, with exact-name and statement/body-shape patterns preserved in enumerate.py; no global semantic absence claim. Full source blobs are hash-bound rather than redundantly dumped. All candidates, hits and source locations preserved without caps.'}
write('SUMMARY.json',summary);print(json.dumps(summary,indent=2))
