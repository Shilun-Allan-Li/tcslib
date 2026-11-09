from pathlib import Path
import subprocess,json,hashlib,re,ast,collections,datetime
O=Path(__file__).parent;W=Path('/Users/seyoonr/.codex/worktrees/ab34-input-readers/tcslib-arora-barak-ch3-4');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');g=lambda p,*a:subprocess.check_output(['git','--no-optional-locks','-C',str(p),*a]);H=lambda b:hashlib.sha256(b).hexdigest();head='1d35e812ce12059b87066d8680748e46553a9137';base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';refs={l.split(' ',1)[0]:l.split(' ',1)[1] for l in g(W,'for-each-ref','--format=%(refname) %(objectname)','refs/heads','refs/remotes').decode().splitlines()};selected={r:h for r,h in refs.items() if not re.search(r'/pr/\d+$',r) and not r.endswith('/HEAD')};(O/'ALL-AVAILABLE-BRANCH-REFS.json').write_text(json.dumps(refs,indent=2)+'\n');groups=collections.defaultdict(list)
for r,h in selected.items():groups[h].append(r)
open8={'241':'codex/ab34-fe-live1','242':'codex/ab34-first-halt-reuse','243':'codex/ab34-ch7-run-reuse','244':'codex/ab34-safe-run-segments','245':'codex/ab34-word-leaves','246':'codex/ab34-restart-reader','247':'codex/ab34-canonoffset-bit-reader','249':'codex/ab34-ladner-statements'};checked8=[]
for pr,branch in open8.items():
 r='refs/heads/'+branch;assert r in selected;checked8.append({'PR':int(pr),'branch':branch,'local_ref':r,'source':selected[r],'available_aliases':[x for x in selected if selected[x]==selected[r]]});g(W,'cat-file','-e',selected[r]+'^{commit}')
blobrefs=collections.defaultdict(list);treecounts=[]
for rev,aliases in groups.items():
 files=[]
 for row in g(W,'ls-tree','-r','-z',rev).split(b'\0'):
  if not row:continue
  spec,p=row.split(b'\t',1);mode,kind,oid=spec.split();p=p.decode()
  if kind==b'blob' and p.startswith('TCSlib/') and p.endswith('.lean'):
   oid=oid.decode();files.append(p);blobrefs[oid].append({'source_kind':'named_source_ref','commit':rev,'refs':aliases,'path':p})
 treecounts.append({'commit':rev,'refs':aliases,'TCSlib_Lean_files':len(files)})
records=g(R,'rev-parse','HEAD^{commit}').decode().strip();prepared=[]
for row in g(R,'ls-tree','-r','-z',records,'--','campaign/items').split(b'\0'):
 if not row:continue
 spec,p=row.split(b'\t',1);mode,kind,oid=spec.split();p=p.decode()
 if kind==b'blob' and p.endswith(('.lean','.lean.txt','.patch')):
  oid=oid.decode();blobrefs[oid].append({'source_kind':'tracked_prepared_source_data','commit':records,'path':p});prepared.append({'path':p,'Git_blob':oid})
# Current prepared worktree bytes are an additional data surface; dirty RO1 is never adopted.
raw_worktrees=g(W,'worktree','list','--porcelain').decode();wt=[]
for block in raw_worktrees.strip().split('\n\n'):
 d={}
 for l in block.splitlines():
  k,_,v=l.partition(' ');d[k]=v
 if d:wt.append(d)
working=[];privatebytes={}
for row in wt:
 p=Path(row.get('worktree',''));branch=row.get('branch','')
 if not p.is_dir() or not ('ab34' in str(p) or 'ab34' in branch):continue
 changed=g(p,'diff','--name-only','HEAD','--','*.lean').decode().splitlines();untracked=g(p,'ls-files','--others','--exclude-standard','--','*.lean').decode().splitlines()
 for path in sorted(set(changed+untracked)):
  q=p/path
  if q.is_file() and '.lake/' not in path:
   b=q.read_bytes();oid='WORKING-SHA256-'+H(b);privatebytes[oid]=b;blobrefs[oid].append({'source_kind':'prepared_worktree_actual_bytes','worktree':str(p),'HEAD':row.get('HEAD'),'branch':branch,'path':path,'tracked_dirty':path in changed});working.append({'worktree':str(p),'HEAD':row.get('HEAD'),'path':path,'bytes':len(b),'sha256':H(b),'tracked_dirty':path in changed})
(O/'WORKTREE-INVENTORY.json').write_text(json.dumps({'all_worktrees':wt,'campaign_worktree_changed_or_untracked_Lean':working},indent=2)+'\n');(O/'REF-COVERAGE.json').write_text(json.dumps({'observed_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':head,'campaign_BASE':base,'current_records':records,'open8':checked8,'selected_named_ref_count':len(selected),'distinct_source_commits':len(groups),'source_ref_tree_counts':treecounts,'prepared_tracked_source_files':prepared,'private_prepared_worktree_source_bytes':working,'exclusions':'Historical numeric refs/remotes/origin/pr/N are not a current open-PR inventory; no remote fetch/query was executed. All available named local/remote branches and their complete TCSlib Lean files are scanned; all tracked campaign/items .lean/.lean.txt/.patch data are additionally scanned. No proof of global absence or freshness beyond these exact observed refs.','scripts_treated_as_data_not_executed':True},indent=2)+'\n')
ids=[x for x in blobrefs if not x.startswith('WORKING-')];raw=subprocess.check_output(['git','--no-optional-locks','-C',str(W),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode());data={};at=0
for oid in ids:
 e=raw.index(b'\n',at);hd=raw[at:e].split();assert hd[0].decode()==oid and hd[1]==b'blob';n=int(hd[2]);at=e+1;data[oid]=raw[at:at+n];at+=n+1
assert at==len(raw);data.update(privatebytes);helper=W/'devtools/seyoon/declfreeze.py';t=ast.parse(helper.read_text());allow={'KW','DECL','ANON','STOP','SCOPE'};ns={'re':re};exec(compile(ast.Module(body=[n for n in t.body if isinstance(n,ast.FunctionDef) or isinstance(n,ast.Assign) and all(isinstance(x,ast.Name) and x.id in allow for x in n.targets)],type_ignores=[]),str(helper),'exec'),ns)
# Remove nested Lean comments while preserving line structure for heuristic source enumeration.
def stripcomments(s):
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif quoted:
   out.append(s[i])
   if s[i]=='\\' and i+1<len(s):i+=1;out.append(s[i])
   elif s[i]=='"':quoted=False
   i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(s[i]);quoted=s[i]=='"';i+=1
 return ''.join(out)
def declheader(c):
 s=stripcomments(c);m=re.search(r'(?m)^(?:private\s+|protected\s+)?(?:def|abbrev|lemma|theorem|instance)\s+',s)
 if not m:return ''
 s=s[m.start():];depth=0;quote=False;i=0
 while i<len(s):
  if s[i]=='"':quote=not quote
  if not quote:
   if s[i] in '({[':depth+=1
   elif s[i] in ')}]':depth-=1
   elif depth==0 and s.startswith(':=',i):return s[:i]
  if s[i]=='\\' and quote:i+=1
  i+=1
 return s
exact=re.compile(r'\b(?:controlAction_eq|inputMoveAction_eq|inputFoldTM_tr_bwd)\b');terms=re.compile(r'\b(?:controlAction|inputMoveAction|inputFoldTM|returnScanTM)\b');candidates=[];rawhits=[];inventory=[];parsefails=[];candidatefiles=O/'candidate-excerpts';candidatefiles.mkdir(exist_ok=True)
for oid,b in data.items():
 s=b.decode('utf-8');clean=stripcomments(s);inventory.append({'Git_blob_or_working_SHA256_key':oid,'bytes':len(b),'sha256':H(b),'occurrences':blobrefs[oid]})
 if not (terms.search(clean) or exact.search(clean) or ('Action' in clean and '⟨' in clean and '=' in clean)):continue
 chunks=list(ns['chunks'](s));covered=set()
 for name,private,c in chunks:
  cc=stripcomments(c);header=declheader(c);flags=[]
  if exact.search(cc):flags.append('EXACT_NEW_NAME_IDENTIFIER')
  if terms.search(header):flags.append('DIRECT_DEFINITION_OR_ALIAS_IN_STATEMENT')
  if 'Action' in header and '=' in header and ('⟨' in header or 'Action.mk' in header):flags.append('ACTION_CONSTRUCTOR_STATEMENT_SHAPE')
  if re.search(r'\binputFoldTM\b',cc) and re.search(r'\bbwd\b',cc) and ('.tr' in cc or re.search(r'\b(?:simp|unfold|dsimp|rw)\b',cc)):flags.append('INLINE_BACKWARD_TABLE_READING_CANDIDATE')
  if not flags:continue
  at=s.find(c);assert at>=0;key=H(c.encode());q=candidatefiles/(key+'.lean.txt');q.write_text(c+'\n');candidates.append({'candidate':len(candidates)+1,'source_blob':oid,'name':name,'private':private,'source_line':s[:at].count('\n')+1,'lines':len(c.splitlines()),'chunk_sha256_without_capture_LF':key,'capture':str(q.relative_to(O)),'flags':flags,'header':header,'source_occurrences':blobrefs[oid]});covered.add(key)
 if exact.search(clean):
  ls=s.splitlines();hits=[{'line':i+1,'text':l} for i,l in enumerate(ls) if exact.search(stripcomments(l))];rawhits.append({'source_blob':oid,'occurrences':blobrefs[oid],'hits':hits})
(O/'SEARCHED-SOURCE-BLOBS.json').write_text(json.dumps(inventory,indent=2)+'\n');(O/'CANDIDATES.json').write_text(json.dumps(candidates,ensure_ascii=False,indent=2)+'\n');(O/'EXACT-NAME-HITS.json').write_text(json.dumps(rawhits,ensure_ascii=False,indent=2)+'\n');summary={'named_refs':len(selected),'distinct_source_ref_commits':len(groups),'all_open_PR_heads':len(checked8),'tracked_prepared_source_paths':len(prepared),'prepared_worktree_byte_files':len(working),'unique_scanned_source_blobs':len(data),'scanned_bytes':sum(len(b) for b in data.values()),'candidate_rows':len(candidates),'distinct_complete_candidate_chunks':len(covered) if False else len({x['chunk_sha256_without_capture_LF'] for x in candidates}),'exact_name_source_blobs':len(rawhits),'heuristic_only':'Bounded enumeration plus subsequent complete-chunk inspection; no global semantic API absence claim and no received script execution.'};(O/'ENUMERATION-SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
