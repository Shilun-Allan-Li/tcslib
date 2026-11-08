from pathlib import Path
import subprocess,hashlib,json,base64,gzip,datetime
P=Path('/private/tmp/sg1-round3-return-review');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
H='79e7c63a6bfa5f002663924f5c7d4e72db705026';K='f07808363a5fc839de9cdb1c90e05158826bbf57';B='3023dc1408c3d216fc07a7cbba9ae30135b861ed';E='f37dab00e3e04b396eb9cf130d3a738385653f71';G='campaign/gates/106-sg1-dedup';EP='arora-barak-ch3-4/outbox/gates/106-sg1-dedup-r3-gate/'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
def save(n,d):(P/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
for r in [H,K,B,E]:
 assert git('rev-parse',r).decode().strip()==r
 subprocess.run(['git','cat-file','-e',r+'^{commit}'],cwd=R,check=True)
f=(R/G/'findings-r3.md').read_bytes();assert(len(f),sha(f))==(23261,'a98e9f12d2e5b75c270edf0e28cc79783505c7b6163cbeacb50536204b1d2cc6');(P/'findings.received.md').write_bytes(f)
q=subprocess.Popen(['git','cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def blob(pin,path):
 q.stdin.write((pin+':'+path+'\n').encode());q.stdin.flush();hdr=q.stdout.readline().decode().strip().split();assert len(hdr)==3 and hdr[1]=='blob',(pin,path,hdr)
 oid,_,n=hdr;n=int(n);b=q.stdout.read(n);assert len(b)==n and q.stdout.read(1)==b'\n';assert hashlib.sha1(b'blob '+str(n).encode()+b'\0'+b).hexdigest()==oid;return oid,b
try:
 sums=blob(E,EP+'SHA256SUMS')[1];checks=[];bundle=None
 for line in sums.decode().splitlines():
  digest,name=line.split('  ',1);oid,b=blob(E,EP+name);assert sha(b)==digest;checks.append({'path':EP+name,'blob':oid,'bytes':len(b),'sha256':digest})
  if name.endswith('-bundle.md'):bundle=b
 assert len(checks)==4 and bundle is not None
 order=blob(E,EP+'BUNDLE-FILES.txt')[1];assert order==blob(K,G+'/BUNDLE-FILES-r3.txt')[1]
 paths=order.decode().splitlines();assert len(paths)==len(set(paths))==1614
 idx=json.loads(blob(E,EP+'INPUT-INDEX.json')[1]);assert(idx['source'],idx['records'],idx['sections'],idx['JSON_parsed'])==(H,K,1614,521)
 assert len(bundle)==100861434 and sha(bundle)=='104d4805fc8e1b53fdc8aa1e8ac7e611b09034398f46887fdc0be4d4e7aeb5d8'
 sections=[];off=0;jcount=0
 for i,path in enumerate(paths):
  pin=H if path.startswith('TCSlib/')else K;oid,b=blob(pin,path);b.decode('utf8')
  if path.endswith('.json'):json.loads(b);jcount+=1
  content=b+(b''if b.endswith(b'\n')else b'\n');body=b'```\n'+content+b'```\n'if path.endswith(('.lean','.py'))else content
  chunk=(b'\n'if i else b'')+('## ===== '+path+' =====\n\n').encode()+body
  assert bundle[off:off+len(chunk)]==chunk,(i,path);off+=len(chunk)
  row={'path':path,'pin':pin,'blob':oid,'bytes':len(b),'sha256':sha(b),'rendered_body_bytes':len(body),'rendered_body_sha256':sha(body)}
  assert row==idx['files'][i],path;sections.append(row)
 assert off==len(bundle)and jcount==521
 save('all1614-section-bindings.json',sections);save('immutable-exchange-checksums.json',checks)
 enc=json.loads(blob(K,G+'/review/round3-final-packet/encoding-receipt.json')[1]);tr=enc['transforms'];assert len(tr)==40 and len({r['encoding_path']for r in tr})==31
 alias=[];represented={}
 for r in tr:
  e=r['encoding_path'];assert e in paths and r['original']['path']not in paths
  coded=blob(K,e)[1];z=base64.b64decode(b''.join(coded.split()),validate=True);raw=gzip.decompress(z);raw.decode('utf8');o=r['original'];oid,b=blob(K,o['path'])
  assert raw==b and(len(raw),sha(raw))==(o['bytes'],o['sha256'])and(len(z),sha(z))==(r['gzip_bytes'],r['gzip_sha256'])and(len(coded),sha(coded))==(r['encoded_utf8_bytes'],r['encoded_utf8_sha256'])
  assert z[4:8]==b'\0\0\0\0'and z[3]&8==0
  represented[o['path']]=e;alias.append({'original':o['path'],'encoding':e,'raw_bytes':len(raw),'raw_sha256':sha(raw),'Git_blob':oid,'lossless':True})
 for r in enc['binary_gzip_equivalents']:
  coded=blob(K,r['represented_by'])[1];raw=base64.b64decode(b''.join(coded.split()),validate=True);oid,b=blob(K,r['path']);assert raw==b and(len(raw),sha(raw))==(r['bytes'],r['sha256']);represented[r['path']]=r['represented_by'];alias.append({'original':r['path'],'encoding':r['represented_by'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'Git_blob':oid,'binary_companion':True,'lossless':True})
 assert len(alias)==43;save('lossless-alias-checks.json',alias)
 capture=json.loads(blob(K,G+'/review/round3-current-source-screen25-final79/capture.json')[1]);assert(capture['base'],capture['head'])==(B,H)and len(capture['population'])==25
 caprows=[]
 for side in ['base','head']:
  for r in capture['sides'][side]['files']:
   path=G+'/review/round3-current-source-screen25-final79/inputs/'+side+'/'+r['path']+'.txt';a,b=blob(K,path);c,d=blob(capture[side],r['path']);assert a==c==r['blob']and b==d and(len(b),sha(b))==(r['bytes'],r['sha256'])and path in paths and path not in represented
   caprows.append({'capture':path,'source':capture[side],'bytes':len(b),'sha256':sha(b),'plaintext_in_packet':True})
 assert len(caprows)==50;save('all50-current-source-captures.json',caprows)
 # Every bundled manifest is data, checked against its exact record-pin member bytes.
 manifests=[]
 for path in paths:
  if not path.endswith('MANIFEST.json'):continue
  data=json.loads(blob(K,path)[1]);rs=data.get('files',data.get('artifacts',[]));checked=[]
  for r in rs:
   if not isinstance(r,dict)or'path'not in r or'sha256'not in r:continue
   member=r['path']if r['path'].startswith(('campaign/','TCSlib/','devtools/'))else path.rsplit('/',1)[0]+'/'+r['path']
   oid,b=blob(K,member);assert sha(b)==r['sha256']and('bytes'not in r or len(b)==r['bytes']),(path,member)
   checked.append({'path':member,'bytes':len(b),'sha256':sha(b),'represented_in_packet':member in paths or member in represented})
  manifests.append({'manifest':path,'schema':'files'if'files'in data else'artifacts','checked_members':len(checked),'members':checked})
 save('bundled-manifest-checks.json',manifests)
 current=json.loads(blob(K,G+'/review/round3-final-packet/QA.json')[1]);folders=[r['folder']for r in current['complete_folder_coverage']]+[G+'/review/round3-final-packet-peer-review',G+'/review/round3-publication-supplement',G+'/review/round3-root-adoption'];coverage=[]
 for folder in folders:
  names=git('ls-tree','-r','--name-only',K,'--',folder).decode().splitlines();missing=[n for n in names if n not in paths and n not in represented];assert not missing,(folder,missing);coverage.append({'folder':folder,'all_files':len(names),'all_direct_or_lossless_alias':True})
 candidate=blob(K,G+'/review/round3-final-packet/BUNDLE-FILES-candidate.txt')[1].decode().splitlines();draft=blob(K,G+'/review/round3-publication-supplement/BUNDLE-FILES-r3-draft.txt')[1].decode().splitlines();assert len(candidate)==1539 and len(draft)==1609 and paths[:1609]==draft and[p for p in paths if p in set(candidate)]==candidate
 graph=blob(K,'devtools/seyoon/graph.py')[1];assert graph==blob(K,G+'/review/round3-publication-supplement/graph.py.txt')[1]and sha(graph)=='c4c1aa599a091c88f77062fd2fca4482ed8017e683819a650e343760ac78d72c'
 save('packet-scope-checks.json',{'folders':coverage,'original1539_all_preserved_in_order':True,'draft1609_exact_prefix':True,'root_append5':paths[1609:],'graph_helper_exact':True})
 save('packet-verification.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':H,'records':K,'comparison_base':B,'exchange':E,'findings_bytes':len(f),'findings_sha256':sha(f),'full_report_rows':27,'major':1,'notes':26,'all1614_rendered_sections_mixed_Git_pins_exact':True,'all521_JSON_parsed':True,'four_exchange_checksums_exact':True,'bundle_bytes':len(bundle),'bundle_sha256':sha(bundle),'all40_substitutions_31_encodings_3binary_companions_verified':True,'all50_plaintext_current_captures_exact':True,'all_declared17folders_complete':True,'manifest_count':len(manifests),'manifest_payload_entries':sum(r['checked_members']for r in manifests),'report_files_schema_manifests':sum(r['schema']=='files'for r in manifests),'report_files_schema_entries':sum(r['checked_members']for r in manifests if r['schema']=='files'),'no_supplied_scripts_executed':True,'no_Lean_or_screen_or_Git_mutations':True})
 print((P/'packet-verification.json').read_text(),flush=True)
finally:
 q.stdin.close();q.stdout.close();q.wait();assert q.returncode==0
