from pathlib import Path
import json,hashlib,subprocess,os,re
P=Path('/private/tmp/ab34-gate128-ready-draft');O=Path('/private/tmp/ab34-gate128-publication-peer');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');V=P/'evidence/actual-validation162';Q=P/'evidence/source-QA119/current';h=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_text());env=dict(os.environ);env['GIT_OPTIONAL_LOCKS']='0'
def w(n,x):(O/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.check_output(['git','-C',str(R),*args],env=env)
# Original frozen components stay original, including original source-name relocations.
components=[]
for c in J(P/'bindings/COMPONENT-RELOCATION.json'):
 D=P/c['destination'];assert h((D/'MANIFEST.json').read_bytes())==c['manifest_SHA256'];m=J(D/'MANIFEST.json');rows=m['files'];assert len(rows)==c['payloads'];mapping={}
 if (D/'ADOPTION.json').exists():mapping={r['original_path']:r['records_path'] for r in J(D/'ADOPTION.json')['mapping']}
 checks=[]
 for r in rows:
  rel=mapping.get(r['path'],r['path']);b=(D/rel).read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256'];b.decode();checks.append({'logical_path':r['path'],'actual_path':rel,'bytes':len(b),'SHA256':h(b)})
 components.append({'component':c['destination'],'manifest_SHA256':c['manifest_SHA256'],'payloads':len(checks),'every_payload_byte_hash_exact':True,'files':checks})
w('frozen-components-checks.json',components)
base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';old='63eb044c55032d8d9570e54e99d520522f2449e5';head='1096e50b4e105392737ec52939b1db0cdbd9316d';trees={}
for ref in [base,old,head]:
 subprocess.run(['git','-C',str(R),'cat-file','-e',ref+'^{commit}'],env=env,check=True);raw=git('ls-tree','-r',ref).decode();trees[ref]={l.split('\t',1)[1]:l.split()[2] for l in raw.splitlines()}
source_maps={}
for label,ref in [('BASE',base),('HEAD',head)]:
 source_maps[label]=J(Q/(label+'-ALL-LEAN-BLOBS.json'));assert source_maps[label]=={p:v for p,v in trees[ref].items() if p.endswith('.lean')}
assert len(source_maps['BASE'])==1003 and len(source_maps['HEAD'])==1004
changed=sorted(p for p in set(source_maps['BASE'])|set(source_maps['HEAD']) if source_maps['BASE'].get(p)!=source_maps['HEAD'].get(p));assert changed==['TCSlib/Complexity/Diagonalization.lean','TCSlib/Complexity/Diagonalization/Ladner.lean'];owner=changed[1];assert owner not in trees[base] and trees[old][owner]==trees[head][owner]
sm=J(V/'inputs/passed-Nlad2/source-before.json');ids=sorted({r['git_blob'] for r in sm.values()}|{trees[base][changed[0]],trees[old][changed[0]]});raw=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=('\n'.join(ids)+'\n').encode(),capture_output=True,env=env,check=True).stdout;pos=0;blobs={}
for oid in ids:
 a=raw.index(b'\n',pos);got,kind,size=raw[pos:a].decode().split();assert got==oid and kind=='blob';size=int(size);b=raw[a+1:a+1+size];assert raw[a+1+size:a+2+size]==b'\n';assert hashlib.sha1(('blob '+str(size)+'\0').encode()+b).hexdigest()==oid;blobs[oid]=b;pos=a+size+2
assert pos==len(raw) and set(sm)==set(source_maps['HEAD']);sr=[]
for path,r in sm.items():
 b=blobs[r['git_blob']];assert r['git_blob']==trees[head][path] and len(b)==r['bytes'] and h(b)==r['sha256'];sr.append({'path':path,**r,'actual_Git_bytes_exact':True})
w('all1004-current-source-checks.json',{'HEAD':head,'BASE':base,'actual_Git_tree_Lean_counts':[1003,1004],'only_changed_Lean_paths':changed,'new_owner_genuinely_absent_at_BASE':True,'all1004_replay_source_records_actual_Git_bytes_exact':True,'rows':sr})
source=blobs[trees[head][owner]].decode();assert source==(P/'source/HEAD'/(owner+'.txt')).read_text()==(V/'inputs/Ladner-actual.lean.txt').read_text();assert h(source.encode())=='166c77cc4d86b0ae1a4e2d32967628cc5f3f4710c7ec5fc0cedbde5c75333311'
def strip_comments(s):
 i=0;out=[]
 while i<len(s):
  if s.startswith('--',i):
   stop=s.find('\n',i);i=len(s) if stop<0 else stop;continue
  if s.startswith('/-',i):
   depth=1;i+=2
   while depth:
    assert i<len(s)
    if s.startswith('/-',i):depth+=1;i+=2
    elif s.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   out.append(' ');continue
  if s[i]=='"':
   a=i;i+=1
   while i<len(s):
    if s[i]=='\\':i+=2;continue
    if s[i]=='"':i+=1;break
    i+=1
   out.append(s[a:i]);continue
  out.append(s[i]);i+=1
 return ''.join(out)
proto=(P/'evidence/prototype132/Ladner-v2.lean.txt').read_text();formal=strip_comments(source);assert formal==strip_comments(proto)==(Q/'HEAD-comment-stripped-full-code.txt').read_text()==(Q/'PROTOTYPE-comment-stripped-full-code.txt').read_text();facade_head=blobs[trees[head][changed[0]]].decode();facade_base=blobs[trees[base][changed[0]]].decode();assert strip_comments(facade_head).replace('import TCSlib.Complexity.Diagonalization.Ladner\n','',1)==strip_comments(facade_base);assert trees[base]['TCSlib.lean']==trees[head]['TCSlib.lean'];decls=re.findall(r'^(?:noncomputable\s+)?(def|theorem|lemma)\s+(\w+)',formal,re.M);assert len(decls)==17 and sum(k=='def' for k,n in decls)==4 and len(re.findall(r'\bsorry\b',formal))==6
w('trusted-source-checks.json',{'HEAD':head,'actual_owner_SHA256':h(source.encode()),'prototype_file_SHA256':h(proto.encode()),'prototype_is_file_not_commit':True,'comment_stripped_full_code_byte_exact_to_prototype_and_QA':True,'new_public_authored_declarations':17,'definitions':4,'proved_readings':6,'direct_mathematical_sorries':6,'dependent_packaging':1,'no_seventh_obligation_or_pending_SAT_reader_or_iterator_import':True,'declarations_as_written':decls,'facade_after_only_authorized_import_removal_code_exact_BASE':True,'root_facade_unchanged_no_root_elaboration_claim':True,'source_edition_fallback_verified_against_recorded_PLAN_not_new2009_book_verification':True})
# All97 full source captures and both pinned package origins.
request=J(P/'screen/REQUEST.json');pop=request['population_common48'];poph=request['population_Ladner49'];assert len(pop)==48 and len(poph)==49 and set(poph)-set(pop)=={owner};capture=[]
for phase,key,ref in [('BASE','BASE',base),('HEAD','LADNER',head)]:
 e=request['exports'][key];assert e['source']==ref and e['files']==(pop if phase=='BASE' else poph)
 for rel in e['files']:
  q=P/'source'/phase/(rel+'.txt');b=q.read_bytes();assert h(b)==e['sha256'][rel];blob=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()
  if rel.startswith('Mathlib/'):
   r=request['Mathlib_files'][rel];assert request['Mathlib_package']==r['package_commit']=='029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e';actual=subprocess.check_output(['git','-C',str(R/'.lake/packages/mathlib'),'rev-parse',r['package_commit']+':'+rel],env=env).decode().strip();assert blob==r['git_blob']==actual
  else:assert blob==trees[ref][rel]
  capture.append({'phase':phase,'path':rel,'capture':q.relative_to(P).as_posix(),'bytes':len(b),'SHA256':h(b),'actual_Git_blob':blob})
assert len(capture)==97 and not (P/'source/BASE'/(owner+'.txt')).exists();w('all97-source-capture-checks.json',{'request_SHA256':h((P/'screen/REQUEST.json').read_bytes()),'BASE48_HEAD49_exact_args':True,'two_Mathlib_package_sources_each_side_actual_Git_exact':True,'BASE_owner_absent_not_fake_empty':True,'rows':capture})
# Real whole snapshots are represented by maps/independent anchors, not exported binaries.
anchors=J(P/'anchors/MAC8/object-hashes.json');assert len(anchors)==895 and anchors==J(V/'MAC8-before.json')==J(V/'mac8-after.json');rep=[]
for phase in ['Nlad1','Nlad2']:
 D=V/'inputs'/('passed-'+phase);req=J(D/'request.json');res=J(D/'RESULT.json');before=J(D/'input-before.json');after=J(D/'input-after.json');output=J(D/'output.json');assert before==after==anchors and len(output)==896;assert set(output)-set(before)=={'TCSlib/Complexity/Diagonalization/Ladner.olean'};assert [p for p in before if before[p]!=output[p]]==['TCSlib/Complexity/Diagonalization.olean'];assert res['pass'] and res['modules']==res['expected_modules']==2 and res['failed']==res['static_exit']==0;assert (D/'static.txt').read_text().strip()=='modules 2, mismatches 0, static total 6'
 rows=J(D/'module-results.json');assert len(rows)==2 and sum(r['sorry'] for r in rows)==6
 for r in rows:
  b=(D/'logs'/(r['module']+'.log')).read_bytes();assert h(b)==r['log_sha256'] and r['exit']==r['errors']==0 and r['fresh_output'] and r['pass'];assert b.count(b"declaration uses 'sorry'")==r['sorry']
 assert output['TCSlib/Complexity/Diagonalization/Ladner.olean']=='6b7b2adeb3182d7c610c75d166eebb66a3cad3ae5752e8cf4a6a44a88ae2fc96';rep.append({'phase':phase,'actual_head':req['head'],'result':res,'input_objects':895,'output_objects':896,'added_owner_only_plus_facade_rewrite':True,'full2_module_logs_and_static_exact':True})
context=J(V/'OWNER-IMPORT-CONTEXT.json');assert len(context['rows'])==115 and context['changed_facade_not_imported'];out1=J(V/'inputs/passed-Nlad1/output.json');out2=J(V/'inputs/passed-Nlad2/output.json');ctx=[]
for r in context['rows']:
 path=r['path'];assert trees[base][path]==trees[old][path]==trees[head][path]==r['Git_blob_BASE_63eb_1096'];assert h(blobs[trees[head][path]])==r['source_SHA256'];op=r['object_path'];assert anchors[op]==out1[op]==out2[op]==r['MAC8_Nlad1_Nlad2_object_SHA256'];ctx.append(dict(r,independent_refs_and_object_maps_exact=True))
assert J(V/'Nlad1-before.json')==J(V/'nlad1-after.json')==out1 and J(V/'nlad2-after.json')==out2
w('replay-and-transport-checks.json',{'actual2_current_replay_HEAD':head,'actual_old_metadata_native_controls_HEAD':old,'owner_source_and_object_identical_old_current':True,'all115_internal_source_and_object_context_rows_exact':True,'scope_excludes_changed_facade':True,'all895_MAC8_map_exact_independent_anchor':True,'Nlad1_map_unchanged_by_plain_checks':True,'no_fresh1096_metadata_or_control_execution_inferred':True,'no_physical895_or896_object_rehash_by_peer':True,'replays':rep,'import_context':ctx})
print(json.dumps({'frozen_component_payloads':sum(c['payloads'] for c in components),'source_records':1004,'source_captures':97,'public_declarations':17,'direct_sorries':6,'replay_modules':2,'input_output_objects':[895,896],'transport_internal_sources_objects':115,'stage':'static precheck only; final49/final manifest still required'}))
