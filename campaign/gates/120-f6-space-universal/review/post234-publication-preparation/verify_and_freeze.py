"""Second data-only pass: all representations, scope, source captures and exact size.
The output is a prospective candidate; final records identity/render remains root-owned.
"""
from pathlib import Path
import json,hashlib,base64,gzip,subprocess,tarfile,io,datetime,re
P=Path('/private/tmp/f6-post234-publication-preparation');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');G='campaign/gates/120-f6-space-universal';F='campaign/fills/f6';REL=G+'/review/post234-publication-preparation';H='073baa518700adc3d4b241cb48d2c78401549309';B='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c';screen=F+'/landing/source-screen23-post234/expanded25';sha=lambda b:hashlib.sha256(b).hexdigest();pin=lambda b:{'bytes':len(b),'sha256':sha(b)}
def load(n):return json.loads((P/n).read_text())
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
paths=(P/'BUNDLE-FILES-final-draft.txt').read_text().splitlines();old=(P/'pre234-1430-list-capture.txt').read_text().splitlines();issued=(R/G/'review/packet-draft/BUNDLE-FILES.issued-immutable.txt').read_text().splitlines();old815=(R/G/'review/packet-draft/BUNDLE-FILES.candidate.txt').read_text().splitlines();assert len(old)==1430 and len(issued)==624 and len(old815)==815 and paths[:1430]==old and paths[:624]==issued
for name in ['verify_and_freeze.py','candidate-verification.json']:
 if REL+'/'+name not in paths:paths.append(REL+'/'+name)
(P/'BUNDLE-FILES-final-draft.txt').write_text('\n'.join(paths)+'\n');assert len(paths)==len(set(paths))
batch=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(rev,path):
 batch.stdin.write((rev+':'+path+'\n').encode());batch.stdin.flush();r=batch.stdout.readline().decode().strip().split();assert len(r)==3 and r[1]=='blob';oid,_,n=r;n=int(n);b=batch.stdout.read(n);assert len(b)==n and batch.stdout.read(1)==b'\n';assert hashlib.sha1(b'blob '+str(n).encode()+b'\0'+b).hexdigest()==oid;return oid,b
cache={}
def data(path):
 if path==G+'/pack.md':return(P/'canonical-pack-draft.md').read_bytes()
 if path==G+'/BUNDLE-FILES.txt':return(P/'BUNDLE-FILES-final-draft.txt').read_bytes()
 if path.startswith(REL+'/'):return(P/Path(path).relative_to(REL)).read_bytes()
 if path not in cache:cache[path]=blob(H,path)[1]if path.startswith('TCSlib/')else(R/path).read_bytes()
 return cache[path]
try:
 inv=load('input-inventory.json');refresh=[]
 for r in inv['files']:
  b=data(r['path']);b.decode('utf8');oldpin={'bytes':r['bytes'],'sha256':r['sha256']}
  if pin(b)!=oldpin:refresh.append({'path':r['path'],'previous_candidate':oldpin,'final_candidate':pin(b),'reason':'prospective list gains final verification files'if r['path']==G+'/BUNDLE-FILES.txt'else'records working-tree candidate chronology; root final rebind remains required'});r.update(pin(b))
 inv['prospective_overrides'][1].update(pin(data(G+'/BUNDLE-FILES.txt')));inv['final_preparation_recheck_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();inv['candidate_recheck_changes']=refresh;save('input-inventory.json',inv)
 aliases={};aliasrows=[]
 for r in load('UTF8-substitution-receipt.json')['all_transforms']:
  p=r['original'];a=r['representation'];raw=data(p);coded=data(a);z=base64.b64decode(b''.join(coded.split()),validate=True);assert pin(raw)==r['raw']and pin(coded)==r['encoded']and pin(z)==r['gzip']and gzip.decompress(z)==raw and a in paths
  assert z[4:8]==b'\0\0\0\0'and z[3]&8==0;raw.decode('utf8');aliases[p]=a;aliasrows.append({'original':p,'representation':a,**pin(raw),'complete_roundtrip':True})
 binaries={}
 for r in load('binary-alias-receipt.json')['all_archives']:
  p=r['original'];a=r['representation'];raw=data(p);coded=data(a);assert pin(raw)==r['raw']and pin(coded)==r['encoded']and base64.b64decode(b''.join(coded.split()),validate=True)==raw and a in paths;binaries[p]=a
 assert len(aliases)==43 and len(binaries)==25
 rep=lambda p:binaries.get(p,aliases.get(p,p))
 assert all(rep(p)in paths for p in old815)
 for folder in [F,G,'campaign/status/2026-11-08-followup119-merge']:
  for q in(R/folder).rglob('*'):
   p=str(q.relative_to(R))
   if q.is_file()and not p.startswith(REL+'/'):assert rep(p)in paths,('missing uncapped scope',p)
 source=load('source-bindings.json')['files'];assert len(source)==25
 for r in source:
  oid,b=blob(H,r['path']);assert oid==r['git_blob']and pin(b)=={'bytes':r['bytes'],'sha256':r['sha256']}and b==data(r['path'])
 c50=load('current50-source-bindings.json')['files'];assert len(c50)==50
 for r in c50:
  oid,b=blob(r['source'],r['source_path']);assert oid==r['blob']and b==data(r['path'])and r['path']in paths and r['path']not in aliases
 capture=json.loads((R/screen/'capture.json').read_text());tarchecks=[]
 for side,rev in [('base',B),('head',H)]:
  raw=base64.b64decode(b''.join((R/screen/(side+'.tar.base64.txt')).read_bytes().split()),validate=True);cap=capture['sides'][side];assert(len(raw),sha(raw))==(cap['archive_bytes'],cap['archive_sha256'])
  with tarfile.open(fileobj=io.BytesIO(raw),mode='r:')as t:
   members=[m for m in t.getmembers()if m.isfile()];assert len(members)==25 and len({m.name for m in members})==25
   assert{m.name for m in members}==set(capture['population'])
   for m in members:assert t.extractfile(m).read()==blob(rev,m.name)[1]
  tarchecks.append({'side':side,'source':rev,'all25_archive_members_exact':True,**pin(raw)})
 bc=json.loads((R/screen/'base-candidates.json').read_text());hc=json.loads((R/screen/'head-candidates.json').read_text());assert len(bc)==1454 and len(hc)==1455
 key=lambda r:(r['a'],r['b'],r['kind'],r['cross_file']);bm={key(r):r for r in bc};hm={key(r):r for r in hc};assert len(bm)==1454 and len(hm)==1455 and all(hm[k]==v for k,v in bm.items())and len(set(hm)-set(bm))==1
 assert screen+'/base-candidates.json'in paths and screen+'/head-candidates.json'in paths and screen+'/base-candidates.json'not in aliases and screen+'/head-candidates.json'not in aliases
 part=load('issued-to-current-partition.json');assert len(part['all624_files'])==624
 for r in part['all624_files']:
  now=data(r['path']);r['current']=pin(now);r['status']='unchanged'if r['issued']==pin(now)else'current source or records generation differs'
  if r['issued']!=pin(now):assert'dull'not in r and'full_issued_capture'in r and pin(data(r['full_issued_capture']))==r['issued']
 save('issued-to-current-partition.json',part)
 draft=data(G+'/pack.md').decode();last='**Deliver your findings as a downloadable file named `gate120-f6-space-universal-findings.md`** (the findings table and the verdict line, no other wrapping), and also paste its content in your reply.';assert draft.rstrip().endswith(last)
 for token in [H,B,'28.908s/28.057s','7.578s/6.151s','6.061s','1385→1396','1454→1455','477526→477688','1070.449s','1140.506s','#234 now MERGED','MF63']:
  assert token in draft,token
 for token in ['still unmerged','Current0d','Final current23','must use23']:assert token not in draft
 report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS data-only final prospective-candidate verification','source':H,'base':B,'original624_exact_prefix':True,'full1430_literal_prefix':True,'full815_and_all_F6_folders_represented':True,'all25_root_sources_exact_git073':True,'all50_current_captures_plaintext_exact':True,'both_complete_archives':tarchecks,'all43_UTF8_original_substitutions_roundtrip':True,'all25_binary_companions_roundtrip':True,'new_raw_candidate_JSONs_plaintext':True,'all1454BASE_scores_persist_soleE3_new':True,'book_context_and_Fintype_limits_retained':True,'delivery_paragraph_exact_and_last':True,'candidate_inventory_refreshes':refresh,'final_records_commit_render_hash_publication_root_owned':True,'no_Lean_screen_supplied_script_or_source_Git_canonical_mutation':True}
 save('candidate-verification.json',report)
 qa=load('QA.json');qa['sections']=len(paths);qa['final_candidate_data_verification']='PASS candidate-verification.json';qa['own_files']=len([q for q in P.rglob('*')if q.is_file()]);qa['new_UTF8_substitutions']=12
 def totals():
  a=b=0
  for i,p in enumerate(paths):
   raw=data(p);raw.decode('utf8');a+=len(raw);b+=len(('## ===== '+p+' =====\n\n').encode())+len(raw)+(0 if raw.endswith(b'\n')else 1)+(8 if p.endswith(('.lean','.py'))else 0)+(1 if i else 0)
  return a,b
 oldtotal=None
 for _ in range(12):
  save('QA.json',qa);rows=[{'path':str(q.relative_to(P)),**pin(q.read_bytes())}for q in sorted(P.rglob('*'))if q.is_file()and q.name not in ['MANIFEST.json','SHA256SUMS']];save('MANIFEST.json',{'utc':report['utc'],'status':'Frozen current post234 publication candidate; root final adoption/records/render pending','source':H,'base':B,'physical_file_count':len(rows)+2,'manifest_excludes':['MANIFEST.json','SHA256SUMS'],'files':rows})
  (P/'SHA256SUMS').write_text(''.join(sha(q.read_bytes())+'  '+str(q.relative_to(P))+'\n'for q in sorted(P.rglob('*'))if q.is_file()and q.name!='SHA256SUMS'))
  v=totals()
  if v==oldtotal:break
  qa['payload_utf8_bytes'],qa['rendered_candidate_bytes']=v;oldtotal=v
 else:raise AssertionError('Size accounting did not stabilize')
 assert totals()==(qa['payload_utf8_bytes'],qa['rendered_candidate_bytes'])and qa['rendered_candidate_bytes']<100*1024*1024
 assert all(REL+'/'+str(q.relative_to(P))in paths for q in P.rglob('*')if q.is_file())and not list(P.rglob('*.lean'))and not list(P.rglob('*.pyc'))
 for r in load('MANIFEST.json')['files']:assert pin((P/r['path']).read_bytes())=={'bytes':r['bytes'],'sha256':r['sha256']}
 print(json.dumps({'sections':len(paths),'own_files':qa['own_files'],'payload_bytes':qa['payload_utf8_bytes'],'exact_rendered_candidate_bytes':qa['rendered_candidate_bytes'],'hosting_margin_bytes':100*1024*1024-qa['rendered_candidate_bytes'],'manifest_sha256':sha((P/'MANIFEST.json').read_bytes()),'pack_sha256':sha(data(G+'/pack.md')),'all_checks_PASS':True},indent=2),flush=True)
finally:
 batch.stdin.close();batch.stdout.close();batch.wait();assert batch.returncode==0
