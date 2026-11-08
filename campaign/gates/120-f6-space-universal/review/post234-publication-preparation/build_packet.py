"""Own data-only F6 packet preparer. No supplied code, Lean, screen or Git mutation.
All source sections use git073; records remain a prospective working-tree candidate.
"""
from pathlib import Path
import json,hashlib,subprocess,datetime,base64,gzip,io,codecs,ast,difflib
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=Path('/private/tmp/f6-post234-publication-preparation');G='campaign/gates/120-f6-space-universal';F='campaign/fills/f6';L=F+'/landing';REL=G+'/review/post234-publication-preparation';OLD=G+'/review/final-publication-preparation';H='073baa518700adc3d4b241cb48d2c78401549309';B='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c';IB='3023dc1408c3d216fc07a7cbba9ae30135b861ed';IK='f41bdaea207724606d8934bfc2c9a823c5dd1e2f';IE='2adb80788611696d2cad6f907285c0c5a197ae09';NOW=datetime.datetime.now(datetime.timezone.utc).isoformat();LIMIT=100*1024*1024
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(b):return {'bytes':len(b),'sha256':sha(b)}
def save(n,d):
 q=P/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
def load(rel):return json.loads((R/rel).read_text())
for r in [H,B,IB,IK,IE]:assert git('rev-parse',r).decode().strip()==r;subprocess.run(['git','cat-file','-e',r+'^{commit}'],cwd=R,check=True)
REC=git('rev-parse','HEAD').decode().strip();subprocess.run(['git','cat-file','-e',REC+'^{commit}'],cwd=R,check=True)
assert git('diff','--name-only',B,H,'--','*.lean').decode().splitlines()==['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']
assert sha(git('show',H+':TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'))=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3'
root_before={str(q.relative_to(R)):pin(q.read_bytes())for q in [(R/G/'pack.md'),(R/G/'BUNDLE-FILES.txt'),(R/G/'STATUS.md')]}
(P/'canonical-held-observed.md').write_bytes((R/G/'pack.md').read_bytes())
(P/'pre234-1430-list-capture.txt').write_bytes((R/G/'BUNDLE-FILES.txt').read_bytes())
draft=(P/'canonical-pack-draft.md').read_bytes();assert draft.decode().rstrip().endswith('**Deliver your findings as a downloadable file named `gate120-f6-space-universal-findings.md`** (the findings table and the verdict line, no other wrapping), and also paste its content in your reply.')
(P/'canonical-held-to-candidate.patch').write_text(''.join(difflib.unified_diff((R/G/'pack.md').read_text().splitlines(True),draft.decode().splitlines(True),fromfile=G+'/pack.md (observed HOLD historical draft)',tofile=G+'/pack.md (prospective current candidate)')))
# Validate both current and historical frozen foundations before accepting their artifacts.
expected={L+'/compiled-accounting-final':'0c8d3487e95c62731d750f2b91f1a93314b64861bffced766d5389885e2faad9',L+'/source-screen23-resumed':'9412b0d8bcdbb4dd28583069c78100e22f7abf69316ec2a5c6292364e815329a',L+'/source-screen23-resumed/final23-current':'2b0c6cf93595fef48fe5bc9eac9ee911e521f309bb4ed831aa4256ad34062f2c',L+'/seam-step-repoint-applied':'318e85633bb50630d9c6f633f6907eb74da5faa7e3f490427c24e60cb2a99671',L+'/seam-step-repoint-preflight':'7fcf7920c7d3922804ef747039b2389065b920e0d2a481e892584679a753ce2c',L+'/replay-mf62':'27ac72195ded51b9d64ed1cebe57b9d13bdb6394a9cf11fa4678a3e6b7f7b586',OLD:'0a30be687afea1f19d5ccffa2f0a85d0d1574d6380b718da789124771436c66c',G+'/review/current-packet-peer-review':'900073ec519119e36ba507d59f49c90a6a7d3ee5bebaa2e1caa494cbb0fbc6cb',G+'/review/post234-context-review':'a62dcbe497ce25f4c83a9f9b6d32cb94c01a3228b41386135d3b356fb96d464c',L+'/replay-mf63':'4da1e19d6508fb9aa593d9e526b725e17a7a70bdd6b7e8dadbf153bdfa5b6515',L+'/source-screen23-post234':'ce6a8fc21048dd711b771f5c735e7ba672d6bc946d36227ab895ffb5bb469589',L+'/source-screen23-post234/expanded25':'36f3054d1e0f878dedd073349aacb191408b46c16e3ae17951eef382c8ee163a','campaign/status/2026-11-08-followup119-merge':'cbb2cd3b2d3dc12ca7d60da8ef661529731279701f16800c2164325193b148f1',L+'/post234-source-merge':''}
frozen=[]
for folder,digest in expected.items():
 q=R/folder;mb=(q/'MANIFEST.json').read_bytes();assert not digest or sha(mb)==digest,(folder,'manifest hash');m=json.loads(mb);rs=m.get('files',m.get('artifacts',[]));assert rs
 for r in rs:assert pin((q/r['path']).read_bytes())=={'bytes':r['bytes'],'sha256':r['sha256']},(folder,r['path'])
 frozen.append({'folder':folder,'manifest_sha256':sha(mb),'payload_entries_verified':len(rs),'all_physical_files':sum(p.is_file()for p in q.rglob('*'))})
save('frozen-foundation-checks.json',{'utc':NOW,'all_hashes_and_members_verified':True,'folders':frozen,'source_proof_unchanged':True,'no_old_data_mutation':True})
old1430=(R/G/'BUNDLE-FILES.txt').read_text().splitlines();old1413=(R/OLD/'BUNDLE-FILES-final-draft.txt').read_text().splitlines();issued=(R/G/'review/packet-draft/BUNDLE-FILES.issued-immutable.txt').read_text().splitlines();old815=(R/G/'review/packet-draft/BUNDLE-FILES.candidate.txt').read_text().splitlines()
assert len(old1430)==len(set(old1430))==1430 and len(old1413)==1413 and old1430[:1413]==old1413 and len(issued)==624 and old1430[:624]==issued and len(old815)==815 and old815[:624]==issued
# Batch immutable Git reads; never invoke any bundled tool.
proc=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(rev,path):
 proc.stdin.write((rev+':'+path+'\n').encode());proc.stdin.flush();a=proc.stdout.readline().decode().strip().split();assert len(a)==3 and a[1]=='blob',(rev,path,a);oid,_,n=a;n=int(n);b=proc.stdout.read(n);assert len(b)==n and proc.stdout.read(1)==b'\n';assert hashlib.sha1(b'blob '+str(n).encode()+b'\0'+b).hexdigest()==oid;return oid,b
cache={}
def mixed(rel):
 if rel==G+'/pack.md':return draft
 if rel.startswith(REL+'/'):return(P/Path(rel).relative_to(REL)).read_bytes()
 if rel not in cache:cache[rel]=blob(H,rel)[1]if rel.startswith('TCSlib/')else(R/rel).read_bytes()
 return cache[rel]
try:
 parts=[];partition=[];previous=load(OLD+'/issued-to-current-partition.json')['all624_files']
 for r,path in zip(previous,issued):
  assert r['path']==path;rev=IB if path.startswith('TCSlib/')else IK;oid,old=blob(rev,path);assert pin(old)==r['issued'];old.decode('utf8');content=old+(b''if old.endswith(b'\n')else b'\n');body=b'```\n'+content+b'```\n'if path.endswith(('.lean','.py'))else content;parts.append(('## ===== '+path+' =====\n\n').encode()+body)
  now=mixed(path);now.decode('utf8');row={'path':path,'issued_pin':rev,'issued_blob':oid,'issued':pin(old),'current':pin(now),'current_binding':'source:'+H if path.startswith('TCSlib/')else'records candidate; root final pin pending','status':'unchanged'if old==now else'current source or records generation differs'}
  if old!=now:
   cap='issued-original-captures/'+path+'.txt';q=P/cap;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(old);row['full_issued_capture']=REL+'/'+cap
  partition.append(row)
 original=b'\n'.join(parts);assert original==blob(IE,'arora-barak-ch3-4/outbox/fills/f6-space-universal/f6-space-universal-bundle.md')[1]and pin(original)=={'bytes':8707327,'sha256':'8fa482702846898f7fa04c4e1b0aa012300b4febaa6385ee8caa869cf14740be'}
 save('issued-to-current-partition.json',{'utc':NOW,'issued_source':IB,'issued_records':IK,'issued_exchange':IE,'issued_sections':624,'issued_bundle':pin(original),'original_bundle_reconstructed_byte_exact':True,'current_source':H,'current_base':B,'observed_records_not_final':REC,'all624_files':partition})
 # Complete logical scope, before reversible substitutions; all old drafts and own history retained.
 scope=set(old1430)|set(old815)
 for folder in [F,G]:
  scope.update(str(q.relative_to(R))for q in(R/folder).rglob('*')if q.is_file()and not str(q.relative_to(R)).startswith(REL+'/'))
 adoption='campaign/status/2026-11-08-followup119-merge';scope.update(str(q.relative_to(R))for q in(R/adoption).rglob('*')if q.is_file())
 screen=L+'/source-screen23-post234/expanded25';cap=load(screen+'/capture.json');assert cap['base']==B and cap['head']==H and len(cap['population'])==25;scope.update(cap['population'])
 source50=[]
 for side,rev in [('base',B),('head',H)]:
  for r in cap['sides'][side]['files']:
   path=screen+'/inputs/'+side+'/'+r['path']+'.txt';oid,data=blob(rev,r['path']);assert oid==r['blob']and pin(data)=={'bytes':r['bytes'],'sha256':r['sha256']}and data==(R/path).read_bytes();scope.add(path);source50.append({'path':path,'source':rev,'source_path':r['path'],'blob':oid,**pin(data),'plaintext_required':True})
 assert len(source50)==50;save('current50-source-bindings.json',{'source':H,'base':B,'all50_plaintext':True,'files':source50})
 tools=['devtools/seyoon/graph.py','devtools/seyoon/mkdownmulti.py','devtools/seyoon/mkreplay.py','devtools/seyoon/mkbundle-mixed.py','devtools/seyoon/verifybundle.py','devtools/seyoon/stage.sh','devtools/seyoon/leanelab.sh','devtools/seyoon/leanelab-o.sh','devtools/seyoon/staticsorry.py','devtools/seyoon/scratch-api/slotrun.sh','devtools/seyoon/declfreeze.py','devtools/seyoon/pairdiff.py','scripts/copy-text-screen-v3.py','scripts/style_lint.py','scripts/campaign_style_lint.py'];scope.update(tools);helper=[]
 for path in tools:
  b=(R/path).read_bytes();imports=[]
  if path.endswith('.py'):
   for n in ast.walk(ast.parse(b.decode())):
    if isinstance(n,ast.Import):imports.extend(q.name for q in n.names)
    elif isinstance(n,ast.ImportFrom):imports.append(n.module)
  helper.append({'path':path,**pin(b),'imports':sorted(set(imports))})
 for name in ['graph.py','mkdownmulti.py','mkreplay.py']:assert(R/'devtools/seyoon'/name).read_bytes()==(R/L/'replay-mf63'/(name+'.txt')).read_bytes()
 (P/'graph.py.txt').write_bytes((R/'devtools/seyoon/graph.py').read_bytes());save('helper-provenance.json',{'helpers':helper,'MF63_generators_and_graph_byte_exact':True,'mixed_pin_rule':'TCSlib/* git073; other paths records candidate','supplied_scripts_executed':False})
 # Every pre-existing alias is exact; retain all old18 and all old31->22 substitutions.
 oldbin=load(OLD+'/binary-alias-receipt.json');binary={};binaryrows=[]
 for row in oldbin['archives']:
  raw=(R/row['original']).read_bytes();coded=(R/row['representation']).read_bytes();assert pin(raw)==row['raw']and pin(coded)==row['encoded']and base64.decodebytes(coded)==raw;binary[row['original']]=row['representation'];binaryrows.append(row|{'status':'preserved old exact alias'})
 assert len(binary)==18
 for path in sorted(scope):
  if path in binary:continue
  raw=(R/path).read_bytes()if not path.startswith('TCSlib/')else mixed(path)
  try:raw.decode('utf8')
  except UnicodeDecodeError:
   alias=path+'.base64.txt';assert(R/alias).is_file(),path;coded=(R/alias).read_bytes();assert base64.decodebytes(coded)==raw;binary[path]=alias;scope.add(alias);binaryrows.append({'original':path,'representation':alias,'raw':pin(raw),'encoded':pin(coded),'status':'new exact binary companion','roundtrip':True})
 assert all(a in scope for a in binary.values());save('binary-alias-receipt.json',{'all_archives':binaryrows,'old18_exact_preserved':True,'old10_original_aliases_preserved':True,'new_binary_companions':len(binary)-18,'all_binary_bytes_represented':True})
 diag=oldbin['optional_diagnostic'];decoder=codecs.getincrementaldecoder('utf8')();count=0;dh=hashlib.sha256()
 with gzip.open(R/L/'compiled-accounting/Fintype-uses-v2.out.gz','rb')as f:
  while chunk:=f.read(4*1024*1024):count+=len(chunk);dh.update(chunk);decoder.decode(chunk)
 decoder.decode(b'',final=True);assert count==diag['raw_bytes']==980644140 and dh.hexdigest()==diag['raw_sha256'];save('optional-diagnostic-data-check.json',{'raw_bytes':count,'raw_sha256':dh.hexdigest(),'complete_streamed_UTF8_gzip_verified':True,'semantic_review_or_execution':False,'required_for_primary_current_census':False})
 encoded={};dedup={};transforms=[]
 for row in load(OLD+'/UTF8-substitution-receipt.json')['transforms']:
  raw=mixed(row['original']);coded=(R/row['representation']).read_bytes();z=base64.decodebytes(coded);assert pin(raw)==row['raw']and pin(coded)==row['encoded']and pin(z)==row['gzip']and gzip.decompress(z)==raw;encoded[row['original']]=row['representation'];dedup[sha(raw)]=(row['representation'],z,coded);transforms.append(row|{'status':'preserved old lossless substitution'})
 assert len(encoded)==31 and len(dedup)==22
 protected=set(old1430)|{r['path']for r in source50}|set(binary.values())
 protected.update(path for path in scope if path.endswith(('/base-candidates.json','/head-candidates.json')))
 for path in sorted(scope):
  if path in binary or path in encoded or path in protected:continue
  raw=mixed(path)
  if not((path.endswith('.json')or path.endswith('.tar.base64.txt'))and len(raw)>250000):continue
  raw.decode('utf8');key=sha(raw)
  if key not in dedup:
   buf=io.BytesIO()
   with gzip.GzipFile(fileobj=buf,mode='wb',filename='',mtime=0,compresslevel=9)as z:z.write(raw)
   z=buf.getvalue();coded=base64.encodebytes(z);alias=REL+'/encodings/'+str(len([p for p in P.glob('encodings/*')if p.is_file()])+1).zfill(3)+'-'+Path(path).name+'.gz.base64.txt';q=P/Path(alias).relative_to(REL);q.parent.mkdir(exist_ok=True);q.write_bytes(coded);dedup[key]=(alias,z,coded)
  alias,z,coded=dedup[key];assert gzip.decompress(base64.decodebytes(coded))==raw;encoded[path]=alias;transforms.append({'original':path,'representation':alias,'raw':pin(raw),'gzip':pin(z),'encoded':pin(coded),'status':'new source-preserving lossless substitution','deterministic':'gzip9/mtime0/empty filename/Base64ASCII','roundtrip':True})
 save('UTF8-substitution-receipt.json',{'all_transforms':transforms,'preserved_old31_originals_22_encodings':True,'new_original_substitutions':len(encoded)-31,'distinct_all_encodings':len(dedup),'old1430_literal_order_preserved':True,'original624_exact_prefix':True,'current50_plaintext_preserved':True,'no_source_capture_raw_score_or_control_log_substituted':True})
 def representation(path):return binary.get(path,encoded.get(path,path))
 # Retain the1430 literal path sequence, stronger than required624 prefix; add full uncapped scope.
 sections=list(old1430)
 for path in sorted(scope):
  v=representation(path)
  if v not in sections:sections.append(v)
 assert sections[:624]==issued and sections[:1430]==old1430
 ownfixed=['README.md','prepare_pack.py','build_packet.py','canonical-pack-draft.md','canonical-pack.patch','canonical-held-observed.md','canonical-held-to-candidate.patch','pack-changes.json','pre234-1430-list-capture.txt','frozen-foundation-checks.json','issued-to-current-partition.json','current50-source-bindings.json','graph.py.txt','helper-provenance.json','binary-alias-receipt.json','optional-diagnostic-data-check.json','UTF8-substitution-receipt.json','folder-coverage.json','input-inventory.json','source-bindings.json','current-context.json','BUNDLE-FILES-final-draft.txt','QA.json','MANIFEST.json','SHA256SUMS']
 for q in sorted(P.rglob('*')):
  if q.is_file():
   path=REL+'/'+str(q.relative_to(P))
   if path not in sections:sections.append(path)
 for name in ownfixed:
  if REL+'/'+name not in sections:sections.append(REL+'/'+name)
 assert len(sections)==len(set(sections))and all(representation(path)in sections for path in scope|set(old815))and all(r['path']in sections for r in source50)
 (P/'BUNDLE-FILES-final-draft.txt').write_text('\n'.join(sections)+'\n')
 # Prospective list adoption is concrete; current1430 literal is separately captured above.
 cache[G+'/BUNDLE-FILES.txt']=(P/'BUNDLE-FILES-final-draft.txt').read_bytes()
 coverage=[]
 for folder in [F,G,adoption]:
  rs=[]
  for q in sorted((R/folder).rglob('*')):
   path=str(q.relative_to(R))
   if not q.is_file()or path.startswith(REL+'/'):continue
   a=representation(path);assert a in sections;rs.append({'original':path,'represented_by':a})
  coverage.append({'folder':folder,'physical_files':len(rs),'all_files_without_caps':True,'files':rs})
 save('folder-coverage.json',{'folders':coverage,'own_new_folder_all_files_selected_by_fixed_names_and_actual_walk':True,'full815_represented':True,'full1430_literal_prefix':True,'new_current_frozen_folders_all_represented':True})
 inventory=[];bindings=[]
 for path in sections:
  if path.startswith(REL+'/'):continue
  b=mixed(path);b.decode('utf8');binding='prospective canonical pack draft'if path==G+'/pack.md'else'prospective canonical list'if path==G+'/BUNDLE-FILES.txt'else'source:'+H if path.startswith('TCSlib/')else'records candidate; root final pin pending';row={'path':path,**pin(b),'binding':binding};inventory.append(row)
  if path.startswith('TCSlib/'):oid,raw=blob(H,path);assert raw==b;bindings.append(row|{'source':H,'git_blob':oid})
 assert len(bindings)==25 and{r['path']for r in bindings}==set(cap['population'])
 save('input-inventory.json',{'utc':NOW,'source':H,'base':B,'observed_records_not_final':REC,'files':inventory,'own_folder_binding':'Own MANIFEST covers all new payloads; no circular self-inventory hash','prospective_overrides':[{'path':G+'/pack.md','draft':REL+'/canonical-pack-draft.md',**pin(draft)},{'path':G+'/BUNDLE-FILES.txt','draft':REL+'/BUNDLE-FILES-final-draft.txt',**pin(cache[G+'/BUNDLE-FILES.txt'])}],'root_must_rebind_after_actual_canonical_adoption_and_records_commit':True})
 save('source-bindings.json',{'source':H,'all25_TCSlib_paths_exact_Git_blobs':True,'files':bindings,'comparison_base':B,'only_source_delta':['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']})
 ms=load(G+'/review/post234-context-review/fresh-validation/summary.json');ss=load(screen+'/summary.json');rr=load(L+'/replay-mf63/receipt.json');assert ms['counts']['Head']['all']==193 and ms['fresh19_scopes_PASS']and ms['fresh72paired_controls_PASS']and ss['all_HEAD_rows_classified']==1455 and rr['head']==H and rr['result']=='PASS'
 save('current-context.json',{'utc':NOW,'source':H,'base':B,'Hierarchy_sha256':'550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3','observed_records_not_final':REC,'#234':'MERGED; wholeMAC5adopted; existing F6 proof unchanged','primary_metadata':ms,'primary_full25_screen':ss,'primary_actual_replay':rr,'pre234_0d_193_23_MF61_MF62_and_peerreview':'literal history only','canonical_before':root_before,'parent_final_records_bind_render_publish_owned':True,'no_gate_or_merge_or_debt_action':True})
 (P/'README.md').write_text('''# F6 post-#234 publication preparation

**Not yet clear to merge: #235 — external Codex audit remains open.**

Concrete records-only pack/list preparation for actual source073 over merged campaignbf64,
unchanged550c59 Hierarchy. Primary current evidence is actual wholeMAC5/MF63, fresh both-endpoint
28.908/28.057 inventory, native7.578/scoped6.151/72paired controls/witness6.061 and full fresh25
screens. Every0d/193/23/oldMF61→MF62/pre234peer record retains its own historical generation.
The required Codex downloadable-findings paragraph is exactly the pack's last paragraph.

The original624 issued path/order prefix and complete1430 earlier final list are literal
prefixes here; full815/full1413+3+14 and all incoming/review/landing/issue/current folders remain
represented without caps. Every old18 binary alias (including the original10) and old31→22
UTF8 substitution survives. Complete new gzip/Base64 mappings are reversible and deduplicated
only on exact raw SHA256. Current50source captures, old source captures, raw scores and controls
remain plaintext. The optional980MB historical rendering is retained losslessly as data only.

All25 root TCSlib sections are read from git073, every other input from the records candidate.
Canonical pack/list are explicitly prospective overrides backed by their exact draft files;
observed HOLD pack and prior1430 list are separately captured. The complete external inventory
covers source/current records, while own MANIFEST covers this folder without circular self
hashes. Root must adopt, rebind all final records after commit, verify actual rendered blobs,
index/checksums/size and publish/dispatch. No future commit or dispatch identity is invented.

Only our standard-library data preparers ran. No supplied script, Lean, screen, source/cache/
snapshot/Git/canonical mutation, commit/push, ruling, gate closure or external dispatch occurred.
''')
 qa={'utc':NOW,'result':'PASS prospective current packet preparation; root adoption/final records/render/publication pending','source':H,'base':B,'sections':len(sections),'original624_exact_prefix':True,'original624_bundle_exact':pin(original),'pre2341430_literal_prefix':True,'full815_and_all_new_folders_represented':True,'all25_source_paths_git073':True,'all50_current_captures_plaintext':True,'all1455_HEAD_candidates_retained_classified':True,'current193_19scope_72controls_conditional_witness_PASS':True,'current_MF63_actual2_wholeMAC5':True,'old229_plus2_only_history':True,'all_old_aliases_preserved':True,'new_binary_aliases':len(binary)-18,'new_UTF8_substitutions':len(encoded)-31,'own_files':0,'payload_utf8_bytes':0,'rendered_candidate_bytes':0,'hosting_limit_bytes':LIMIT,'records_pin_finalization_root_owned':True,'no_canonical_source_frozen_or_Git_mutation':True,'no_supplied_scripts_Lean_or_screens_executed':True,'no_circular_candidate_bundle_hash_claimed':True}
 def totals():
  payload=render=0
  for i,path in enumerate(sections):
   b=mixed(path);b.decode('utf8');payload+=len(b);render+=len(('## ===== '+path+' =====\n\n').encode())+len(b)+(0 if b.endswith(b'\n')else 1)+(8 if path.endswith(('.lean','.py'))else 0)+(1 if i else 0)
  return payload,render
 last=None
 for _ in range(12):
  qa['own_files']=sum(q.is_file()for q in P.rglob('*'))+int(not(P/'QA.json').exists())+int(not(P/'MANIFEST.json').exists())+int(not(P/'SHA256SUMS').exists());save('QA.json',qa)
  rs=[{'path':str(q.relative_to(P)),**pin(q.read_bytes())}for q in sorted(P.rglob('*'))if q.is_file()and q.name not in ['MANIFEST.json','SHA256SUMS']];save('MANIFEST.json',{'utc':NOW,'status':'Frozen own current publication candidate; root final adoption/render/records bind pending','source':H,'base':B,'physical_file_count':len(rs)+2,'manifest_excludes':['MANIFEST.json','SHA256SUMS'],'files':rs})
  (P/'SHA256SUMS').write_text(''.join(sha(q.read_bytes())+'  '+str(q.relative_to(P))+'\n'for q in sorted(P.rglob('*'))if q.is_file()and q.name!='SHA256SUMS'))
  now=totals()
  if now==last:break
  qa['payload_utf8_bytes'],qa['rendered_candidate_bytes']=now;last=now
 else:raise AssertionError('Size accounting did not stabilize')
 assert totals()==(qa['payload_utf8_bytes'],qa['rendered_candidate_bytes'])and qa['rendered_candidate_bytes']<LIMIT,qa
 assert all(REL+'/'+str(q.relative_to(P))in sections for q in P.rglob('*')if q.is_file())
 for folder,digest in expected.items():assert sha((R/folder/'MANIFEST.json').read_bytes())==next(x['manifest_sha256']for x in frozen if x['folder']==folder)
 assert root_before=={path:pin((R/path).read_bytes())for path in root_before},'root canonical changed during preparation'
 print(json.dumps({'folder':str(P),'sections':len(sections),'source_paths':len(bindings),'own_files':qa['own_files'],'payload_bytes':qa['payload_utf8_bytes'],'rendered_candidate_bytes':qa['rendered_candidate_bytes'],'manifest_sha256':sha((P/'MANIFEST.json').read_bytes()),'draft_sha256':sha(draft),'new_binary':len(binary)-18,'new_UTF8_substitutions':len(encoded)-31},indent=2),flush=True)
finally:
 proc.stdin.close();proc.stdout.close();proc.wait();assert proc.returncode==0
