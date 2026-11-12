from pathlib import Path
import json,hashlib,subprocess,os,re
P=Path('/private/tmp/ab34-gate122-fh13-frozen');O=Path('/private/tmp/ab34-gate122-publication-peer');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');J=lambda p:json.loads(p.read_text());h=lambda b:hashlib.sha256(b).hexdigest();env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0'
def w(n,x):(O/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def tree(ref):
 s=subprocess.check_output(['git','-C',str(R),'ls-tree','-r',ref],env=env).decode();return {l.split('\t',1)[1]:l.split()[2] for l in s.splitlines() if l.split('\t',1)[1].endswith('.lean')}
base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';old='e0b7fd50ca81d9b8f3dd486f120292da1b4fb880';head='f3c8c050ef98375bc237c72bde74f83d33833374';trees={r:tree(r) for r in [base,old,head]};assert all(len(t)==1003 for t in trees.values());C=P/'inputs/current77'
for label,ref in [('BASE',base),('E0B',old),('HEAD',head)]:assert J(C/(label+'-ALL-LEAN-BLOBS.json'))==trees[ref]
changed=sorted(p for p in trees[head] if trees[head][p]!=trees[base][p]);assert len(changed)==8;between=sorted(p for p in trees[head] if trees[head][p]!=trees[old][p]);assert between==['TCSlib/Complexity/TuringMachine/Universal.lean','TCSlib/Complexity/TuringMachine/UniversalStartup.lean']
sm=J(P/'replay-current153/source-before.json');assert len(sm)==1003;ids=sorted({r['git_blob'] for r in sm.values()}|{trees[base][p] for p in changed}|{trees[old][p] for p in changed});raw=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode(),capture_output=True,env=env,check=True).stdout;blobs={};pos=0
for oid in ids:
 a=raw.index(b'\n',pos);oid2,kind,n=raw[pos:a].decode().split();assert oid2==oid and kind=='blob';n=int(n);b=raw[a+1:a+1+n];assert raw[a+1+n:a+2+n]==b'\n';assert hashlib.sha1(('blob '+str(n)+'\0').encode()+b).hexdigest()==oid;blobs[oid]=b;pos=a+n+2
assert pos==len(raw);srcrows=[]
for path,r in sm.items():
 assert trees[head][path]==r['git_blob'];b=blobs[r['git_blob']];assert len(b)==r['bytes'] and h(b)==r['sha256'];srcrows.append({'path':path,**r,'actual_Git_bytes_exact':True})
# Every complete current44 source comes from the source pin, including unchanged foreign homes.
for phase,ref in [('BASE',base),('HEAD',head)]:
 files=list((P/'source'/phase).rglob('*.lean.txt'));assert len(files)==44
 for p in files:
  rel=p.relative_to(P/'source'/phase).as_posix().removesuffix('.txt');b=p.read_bytes();assert hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()==trees[ref][rel]
rootrows=J(P/'source-review13/CHANGED-ROOT-SOURCE-REVIEW13.json');freeze=J(P/'HEADER-FREEZE13.json');assert len(rootrows)==len(freeze)==13;targets=[];reversed_sources={p:blobs[trees[head][p]].decode() for p in changed}
for r in rootrows:
 path=r['path'];parts={}
 for phase,ref in [('BASE',base),('HEAD',head)]:
  b=(P/r[phase]['complete_chunk']).read_bytes();assert h(b)==r[phase]['complete_chunk_sha256'];s=blobs[trees[ref][path]].decode();assert h(s.encode())==r[phase]['full_source_sha256'];chunk=b.decode();assert chunk in s;assert r['literal_complete_header'] in chunk;parts[phase]=chunk
 assert r['literal_header_privacy_name_exact'];assert reversed_sources[path].count(parts['HEAD'])==1;reversed_sources[path]=reversed_sources[path].replace(parts['HEAD'],parts['BASE'],1);targets.append({'id':r['id'],'path':path,'name':r['name'],'family':r['family'],'literal_header_exact':True,'BASE_SHA256':h(parts['BASE'].encode()),'HEAD_SHA256':h(parts['HEAD'].encode()),'full_doc_header_body_actual_source_bound':True})
assert all(reversed_sources[p]==blobs[trees[base][p]].decode() for p in changed);dc=J(C/'DECLARATION-COMPARISON13.json');assert len(dc['full_changed_declarations'])==13 and dc['all_non_target_declaration_chunks_literal_exact'] and dc['all13literal_headers_exact']
w('source1003-and13-root-checks.json',{'BASE':base,'historical_E0B':old,'HEAD':head,'all1003_current_source_Git_SHA_bytes_exact':True,'complete44_per_phase_Git_bound':True,'changed_owner_paths':changed,'only2_changed_owners_since_E0B':between,'reverse13_complete_target_chunks_recovers_entire8_BASE_owners':True,'all_existing_imports_definitions_names_headers_attributes_other_bytes_exact':True,'no_new_source_admission_or_API_import_name_home_route':True,'source_counts':{'public':dc['total_public'],'private':dc['total_private']},'targets':targets,'all1003_source_rows':srcrows})
# Full chained actual replay, not a composed snapshot or a fresh375-module run.
D0=P/'inputs/historical-fh10-e0b/replay';D1=P/'replay-current153';rep=[];maps={}
for label,D,ref,count in [('historical222',D0,old,222),('current153',D1,head,153)]:
 rq=J(D/'request.json');rr=J(D/'RESULT.json');mods=(D/'down.txt').read_text().splitlines();mr=J(D/'module-results.json');assert rq['head']==rr['head']==ref and rr['pass'] and rr['modules']==rr['expected_modules']==len(mr)==len(mods)==count and rr['failed']==rr['static_exit']==0;assert [r['module'] for r in mr]==mods and 'TCSlib'not in mods
 for r in mr:
  b=(D/'logs'/(r['module']+'.log')).read_bytes();assert h(b)==r['log_sha256'] and r['exit']==r['errors']==0 and r['pass'] and r['fresh_output'];assert b.count(b'error:')==0 and b.count(b"declaration uses 'sorry'")==r['sorry']
 st=(D/'static.txt').read_text();assert re.search(r'modules '+str(count)+r', mismatches 0, static total 31',st)
 before=J(D/'input-before.json');after=J(D/'input-after.json');out=J(D/'output.json');assert before==after and len(before)==len(out)==895 and set(before)==set(out);maps[label]={'before':before,'output':out};rep.append({'label':label,'actual_head':ref,'modules':count,'static_mismatches_total':[0,31],'input_output_objects':[895,895],'all_module_logs_exit_hash_counts_exact':True,'result':rr})
assert maps['historical222']['output']==maps['current153']['before'];assert J(D1/'previous-output-map.json')==maps['current153']['before'];currentchanged=[p for p in maps['current153']['before'] if maps['current153']['before'][p]!=maps['current153']['output'][p]];assert currentchanged==['TCSlib/Complexity/TuringMachine/Universal.olean','TCSlib/Complexity/TuringMachine/UniversalStartup.olean']
anchors=P/'inputs/historical-fh10-e0b/anchors';anchor_candidates=list(anchors.rglob('*object*.json'));matches=[]
for p in anchor_candidates:
 try:
  if J(p)==maps['historical222']['before']:matches.append(p.relative_to(P).as_posix())
 except (ValueError,TypeError):pass
assert matches;original=R/'campaign/status/2026-11-08-mig1-merge/object-hashes.json';assert J(original)==maps['historical222']['before']
compiled=J(D1/'COMPILED-SOURCE-MAP153.json');rows=compiled['files'] if isinstance(compiled,dict) else compiled;assert len(rows)==153
for r in rows:
 path=r['source_path'];p=D1/'compiled-source'/(path+'.txt');b=p.read_bytes();assert h(b)==r['source_sha256'] and len(b)==r['source_bytes'] and r['source_commit']==head and r['source_blob']==trees[head][path] and hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()==trees[head][path]
w('actual222-to153-replay-checks.json',{'historical222_head':old,'current153_head':head,'all895_current_input_before_after_exact_whole_previous_output':True,'independent_original_MAC8_before_historical222_exact':True,'current_output895_changed_only':currentchanged,'all742_objects_outside153_closure_unchanged':True,'all153_compiled_source_captures_actual_Git_SHA_exact':True,'31_inherited_admissions_not_new_or_global_tree_clearance':True,'not375_unique_modules_or_fresh222_at_current':True,'no_physical895_snapshot_rehash_or_new_Lean_by_peer':True,'actual_replays':rep,'anchor_paths':matches})
print(json.dumps({'source_records':1003,'complete_sources_each':44,'changed_owners':8,'complete_literal_roots':13,'all_other_owner_bytes_exact':True,'historical_current_modules':[222,153],'current_input_whole_previous_output':895,'current_changed_objects':len(currentchanged),'static_admissions':31}))
