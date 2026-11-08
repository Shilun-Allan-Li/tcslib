from pathlib import Path
import json,subprocess,hashlib,sys,collections,re
sys.dont_write_bytecode=True
O=Path(__file__).parent;T=json.loads((O/'TASK.json').read_text());W=Path(T['source_worktree']);C=O/'source-census';sys.path.insert(0,'/private/tmp/ab34-fe-live1-final-validation/EXPORT/helpers/devtools/seyoon');from graph import imports_of
sha=lambda b:hashlib.sha256(b).hexdigest()
def full_header(text):
 m=re.search(r':= by(?:\n|$)',text)
 assert m is not None,'missing known theorem body delimiter'
 return text[:m.start()]

def git(*a):return subprocess.check_output(['git','--no-optional-locks','-C',str(W),*a])
def save(p,b):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
assert git('rev-parse','HEAD').decode().strip()==T['source_head'];h=json.loads((O/'PATCH-ATTEMPTS.json').read_text());assert len({r['id'] for r in h})==13 and {r['id'] for r in h}=={r['id'] for r in T['todo']} and all(r['native_PASS'] for r in h)
paths=sorted({r['path'] for r in T['todo']});assert sorted(git('diff','--name-only',T['source_head'],'--','*.lean').decode().splitlines())==paths
new=[];owners=[]
for p in paths:
 final=(W/p).read_bytes();text=final.decode();start=(O/'source/START'/(p+'.txt')).read_bytes();restored=text
 for r in [r for r in T['todo'] if r['path']==p]:
  newchunk=(O/'new-chunks'/(str(r['id'])+'.lean.txt')).read_text();oldchunk=(O/r['block']).read_text();assert text.count(newchunk)==1;assert 'Nat.find' not in newchunk and 'MultiTapeTM.exists_first_halt' in newchunk;assert full_header(newchunk)==full_header(oldchunk);restored=restored.replace(newchunk,oldchunk)
  hr=next(x for x in reversed(h) if x['id']==r['id']);new.append({'id':r['id'],'name':r['name'],'path':p,'old_complete_chunk':r['block'],'new_complete_chunk':'new-chunks/'+str(r['id'])+'.lean.txt','old_chunk_sha256':sha(oldchunk.encode()),'new_chunk_sha256':sha(newchunk.encode()),'literal_header':full_header(oldchunk),'literal_header_exact':True,'new_first_halt_reproof_removed':True,'canonical_API':'Turing.MultiTapeTM.exists_first_halt','native_run':hr['native_run'],'route':r['route'],'no_statement_name_import_API_home_or_design_change':True})
 assert restored.encode()==start,p;save(O/'source/FINAL'/(p+'.txt'),final);assert imports_of(O/'source/START'/(p+'.txt'))==imports_of(O/'source/FINAL'/(p+'.txt'))
 last=next(x for x in reversed(h) if x['path']==p);run=json.loads((O/last['native_run']).read_text());assert run['PASS'] and run['source_sha256']==sha(final)
 owners.append({'path':p,'START_blob':git('rev-parse',T['source_head']+':'+p).decode().strip(),'START_sha256':sha(start),'FINAL_sha256':sha(final),'all_other_bytes_recovered_exact':True,'imports_exact':True,'final_native_run':last['native_run']})
sourcepaths=sorted({r['path'] for r in T['all17_plus_canonical_dispositions']})
for p in sourcepaths:
 start=git('show',T['source_head']+':'+p);base=git('show',T['baseline']+':'+p);save(O/'source/START'/(p+'.txt'),start);save(O/'source/BASE'/(p+'.txt'),base);save(O/'source/FINAL'/(p+'.txt'),(W/p).read_bytes())
full=[]
for r in T['all17_plus_canonical_dispositions']:
 row={'original_inspection':r,'id':r['id'],'path':r['path'],'name':r['name'],'canonical_API':r['canonical_API'],'route':r['route'],'old_complete_chunk':'source-census/'+r['block']};p=r['path'];old=(C/r['block']).read_text();src=(W/p).read_text();header=full_header(old);assert src.count(header)==1,(r['id'],'header not literalonce');at=src.index(header)
 if r['id'] in {x['id'] for x in T['todo']}:
  chunk=(O/'new-chunks'/(str(r['id'])+'.lean.txt')).read_text();row['status']='new13 re-point; actual per-step owner pass';row['native_run']=next(x['native_run'] for x in reversed(h) if x['id']==r['id'])
 elif r['id']==76:
  chunk=old;assert src.count(old)==1;row['status']='canonical home retained; not a consumer copy';row['new_native_execution']=False
 else:
  base=(O/'source/BASE'/(p+'.txt')).read_text();assert base.count(old)==1;end=base.index(old)+len(old);post=base[end:end+200]
  if post:
   assert src.count(post)==1,(r['id'],'boundary not exactonce');stop=src.index(post,at);chunk=src[at:stop]
  else:chunk=src[at:]
  assert chunk.startswith(header);assert 'Nat.find' not in chunk and 'MultiTapeTM.exists_first_halt' in chunk,(r['id'],'not original re-point');row['status']='root original4 re-point already present in START; historical root execution not relabeled';row['new_native_execution']=False
 d=O/'complete17-plus-canonical-chunks'/(str(r['id'])+'-'+r['name'].replace('.','_')+'.lean.txt');save(d,chunk.encode());row.update({'final_complete_chunk':str(d.relative_to(O)),'final_chunk_sha256':sha(chunk.encode()),'final_owner_sha256':sha(src.encode()),'final_line':src[:at].count('\n')+1,'literal_old_new_header_exact':True,'complete_literal_header':header,'final_source_is_uncommitted_delta_over':T['source_head'],'new_import_or_API_or_statement_or_home_or_debt_permission':False});full.append(row)
for r in json.loads((C/'NONMATCHING-EXCLUSIONS.json').read_text()):assert (W/r['path']).read_text().count((C/r['block']).read_text())==1,(r['id'],'out-of-scope source chunk changed')

for attempt in h:
 original=(O/attempt['original_chunk_file']).read_text(); before=(O/attempt['old_chunk_file']).read_text(); after=(O/attempt['new_chunk_file']).read_text(); assert full_header(original)==full_header(before)==full_header(after),('attempt header mismatch',attempt['attempt'])
(O/'ALL-ATTEMPT-FULL-HEADERS.json').write_text(json.dumps({'PASS':True,'attempts':len(h),'complete_headers_including_statement_let_assignments':True,'comparison':'Known outer theorem := by delimiter, not first := which can occur inside a statement let.'},indent=2)+'\n')
(O/'DISPOSITIONS17-PLUS-CANONICAL.json').write_text(json.dumps(full,indent=2)+'\n');(O/'SOURCE-MAP13.json').write_text(json.dumps(new,indent=2)+'\n');(O/'SOURCE-PRESERVATION.json').write_text(json.dumps({'PASS':True,'START_head':T['source_head'],'new_consumers':13,'new_owners':11,'full_consumers':17,'canonical_home':1,'all13_headers_literal_exact':True,'all_other_START_source_bytes_recovered_exact':True,'all_imports_exact':True,'only_11_authorized_source_files_modified':True,'nonmatching_ND4_and_mixed1_chunks_unchanged':True,'owners':owners},indent=2)+'\n');patch=git('diff','--no-ext-diff','--no-color',T['source_head'],'--','*.lean');(O/'remaining13.patch').write_bytes(patch);(O/'all17-since-MAC8.patch').write_bytes(git('diff','--no-ext-diff','--no-color',T['baseline'],'--','*.lean'));print(json.dumps({'source_recovery':'PASS','new_consumers':13,'new_owners':11,'all_consumers':17,'canonical':1,'patch_sha256':sha(patch),'patch_bytes':len(patch)},indent=2))
