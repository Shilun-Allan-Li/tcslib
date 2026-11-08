from pathlib import Path
import json,hashlib,gzip,base64,re,collections,datetime
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/gates/106-sg1-dedup/review/round4-publication-preparation';O=Path('/private/tmp/g106-r4-preparation-peer-review');REL=str(P.relative_to(R));G=R/'campaign/gates/106-sg1-dedup';sha=lambda b:hashlib.sha256(b).hexdigest()
def save(n,d):(O/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
manifest=(P/'MANIFEST.json').read_bytes();assert sha(manifest)=='35b91f91392be7f8c194ce273d7bf06811442b60b84f9bdbc74026cda76afdf1';m=json.loads(manifest)
for r in m['files']:
 b=(P/r['path']).read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256'])
before=[{'path':str(q.relative_to(P)),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(P.rglob('*'))if q.is_file()];assert len(before)==173;save('reviewed-folder-before.json',before)
inv=json.loads((P/'external-input-inventory.json').read_text());enc=json.loads((P/'encoding-receipt-r4.json').read_text());logical=(P/'ORDERED-LOGICAL-INPUTS.txt').read_text().splitlines();physical=(P/'BUNDLE-FILES-r4-draft.txt').read_text().splitlines();prefix=(P/'R3-1614-prefix.txt').read_text().splitlines();assert len(logical)==len(set(logical))==2198 and len(physical)==len(set(physical))==1628 and len(prefix)==1614 and logical[1:1615]==prefix and logical==(P/'BUNDLE-FILES-r4-full-prefix-draft.txt').read_text().splitlines()
rows={r['path']:r for r in inv['rows']};assert len(rows)==2086
for r in enc['mappings']:
 if r['path']in rows:assert all(rows[r['path']][k]==r[k]for k in ['bytes','sha256','render_path','codec'])
 else:rows[r['path']]=r
sources=json.loads((P/'current-source-bindings.json').read_text())['files'];assert len(sources)==50;heads={r['path']:r for r in sources if r['side']=='head'};assert len(heads)==25
shadow=O/'HANDOFF-candidate-frozen-copy.txt';drifts=[];resolved={}
def read_payload(p):
 if p in resolved:return resolved[p]
 if p=='campaign/gates/106-sg1-dedup/pack-r4.md':b=(P/'canonical-pack-r4-draft.md').read_bytes()
 elif p.startswith('TCSlib/'):b=(R/heads[p]['capture']).read_bytes()
 else:b=(R/p).read_bytes()
 if p=='campaign/maintainer/HANDOFF.md':
  rr=rows[p]
  if(len(b),sha(b))!=(rr['bytes'],rr['sha256']):
   old=shadow.read_bytes();assert(len(old),sha(old))==(rr['bytes'],rr['sha256']);drifts.append({'path':p,'candidate_bytes':rr['bytes'],'candidate_sha256':rr['sha256'],'current_bytes':len(b),'current_sha256':sha(b),'independent_frozen_candidate_shadow':'campaign/gates/106-sg1-dedup/review/round4-preparation-peer-review/HANDOFF-candidate-frozen-copy.txt','copy_origin':'separately frozen gate118 preparation chronology snapshot, identical50321bytes/SHA6c1e130c3e1116a0ddb8ea701b16803d181a328ca57ce2c7814b09f63dea13f9','meaning':'expected administrative chronology rebind; candidate exact render can be reconstructed from a separately frozen old body; final current records still root-owned'});b=old
 b.decode('utf8');resolved[p]=b;return b
for p in logical:
 if p not in rows:
  assert p.startswith(REL+'/')and p in physical,p;b=(R/p).read_bytes();rows[p]={'path':p,'bytes':len(b),'sha256':sha(b),'render_path':p,'codec':'identity UTF8','binding_source':'own frozen manifest'}
assert set(rows)==set(logical)
def decode(p,codec):
 b=read_payload(p)
 if codec=='identity UTF8':return b
 payload=b.split(b'base64:\n',1)[1]if b'base64:\n'in b else b
 z=base64.b64decode(payload)
 if codec=='gzip+base64':return gzip.decompress(z)
 assert codec=='base64 of original gzip bytes',codec;return z
verified=[];used=collections.Counter();decodedcache={};actual_drifts=[]
for p in logical:
 r=rows[p];assert r['render_path']in physical,p;key=(r['render_path'],r['codec']);used[key[0]]+=1
 if key not in decodedcache:decodedcache[key]=decode(*key)
 b=decodedcache[key];assert(len(b),sha(b))==(r['bytes'],r['sha256']),(p,r['codec'],len(b),sha(b),r['bytes'],r['sha256'])
 if p.startswith('TCSlib/'):actual=(R/heads[p]['capture']).read_bytes()
 elif p=='campaign/gates/106-sg1-dedup/pack-r4.md':actual=(P/'canonical-pack-r4-draft.md').read_bytes()
 else:actual=(R/p).read_bytes()
 if actual!=b:
  assert p=='campaign/maintainer/HANDOFF.md',p;actual_drifts.append(p)
 verified.append({'path':p,'bytes':len(b),'sha256':sha(b),'carrier':r['render_path'],'codec':r['codec'],'restored_exact':True})
assert set(used)==set(physical)and len(actual_drifts)==len(drifts)==1;assert len(enc['mappings'])==2198-1628==570;save('all2198-logical-restoration.json',verified);save('administrative-rebind-required.json',drifts)
# Native current50 source captures and all25 root source bindings stay literal plaintext.
sourcechecks=[]
for r in sources:
 b=(R/r['capture']).read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256']);blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==r['blob'];assert r['capture']in physical and rows[r['capture']]['codec']=='identity UTF8'and rows[r['capture']]['render_path']==r['capture']
 if r['side']=='head':assert r['source']=='078263a74fe90b92aa6228cf20e43726138afbe6'and r['path']in physical and read_payload(r['path'])==b
 else:assert r['source']=='750987d674899d97db3c73c7278c891fa8772b40'
 sourcechecks.append({'path':r['path'],'side':r['side'],'blob':blob,'plaintext':True,'exact_root_source'if r['side']=='head'else'exact_baseline_capture':True})
save('source-binding-checks.json',sourcechecks)
# Reconstruct the issued1614-section bundle from actual old bindings, including changed bytes.
old=json.loads((P/'issued-r3-reconstruction.json').read_text());assert len(old['rows'])==1614;oldhash=hashlib.sha256();nbytes=0;oldrows=[]
def segment(p,b):
 b.decode('utf8');ending=b''if b.endswith(b'\n')else b'\n';f=b'```\n'if p.endswith(('.lean','.py'))else b'';return('## ===== '+p+' =====\n\n').encode()+f+b+ending+f
for i,r in enumerate(old['rows']):
 assert r['ordinal']==i+1 and r['path']==prefix[i]
 p=r['issued_bytes_binding'];b=read_payload(p)if p.startswith('TCSlib/')else(R/p).read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256']),(r['path'],p)
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==r['issued_blob'],r['path'];seg=segment(r['path'],b)
 if i:oldhash.update(b'\n');nbytes+=1
 oldhash.update(seg);nbytes+=len(seg);oldrows.append({'ordinal':i+1,'path':r['path'],'old_binding':p,'bytes':len(b),'sha256':sha(b),'blob':blob,'exact_old_bytes':True})
assert(nbytes,oldhash.hexdigest())==(100861434,'104d4805fc8e1b53fdc8aa1e8ac7e611b09034398f46887fdc0be4d4e7aeb5d8');save('all1614-issued-reconstruction.json',{'rows':oldrows,'bytes':nbytes,'sha256':oldhash.hexdigest(),'exact':True})
# Current draft physical rendering, with old administrative candidate bytes explicitly distinguished.
curhash=hashlib.sha256();cbytes=0
for i,p in enumerate(physical):
 seg=segment(p,read_payload(p))
 if i:curhash.update(b'\n');cbytes+=1
 curhash.update(seg);cbytes+=len(seg)
assert cbytes==73542214 and cbytes<104857600;save('independent-render.json',{'physical_sections':1628,'bytes':cbytes,'sha256':curhash.hexdigest(),'reconstructed_frozen_candidate_not_final_publication':True,'administrative_shadow_used':drifts,'final_records_source_root_actual_stage_required':True})
# Verify all18 compressed raw streams and old40→31 encodings/three companions as data.
archives=json.loads((P/'current-18-archive-verification.json').read_text())['archives'];C=G/'review/round4-compiled-and-seals';assert len(archives)==18
for r in archives:
 z=(C/r['gzip']).read_bytes();coded=(C/r['base64']).read_bytes();assert base64.b64decode(coded)==z and(len(z),sha(z))==(r['gzip_bytes'],r['gzip_sha256']);raw=gzip.decompress(z);assert(len(raw),sha(raw))==(r['raw_bytes'],r['raw_sha256'])
prior=json.loads((P/'inherited-r3-alias-verification.json').read_text());assert prior['originals']==40 and prior['encodings']==31 and len(prior['transforms'])==40
for r in prior['transforms']:
 b=decode(r['encoding_path'],'gzip+base64');assert(len(b),sha(b))==(r['original']['bytes'],r['original']['sha256']);assert b==(R/r['original']['path']).read_bytes()
assert len(prior['binary_companions'])==3
for r in prior['binary_companions']:
 b=base64.b64decode((R/r['represented_by']).read_bytes());assert(len(b),sha(b))==(r['bytes'],r['sha256'])and b==(R/r['path']).read_bytes()
# Every declared complete current folder is included as logical originals, without a cap.
folders=['review/round4-source-screen25','review/round4-compiled-and-seals','evidence/replay-msg8','review/round4-live-prefix-repair','review/round3-return-review','review/round3-render-peer-qa','review/round4-root-accounting-check'];folderchecks=[]
for folder in folders:
 d=G/folder;ps=sorted(str(q.relative_to(R))for q in d.rglob('*')if q.is_file());assert set(ps)<=set(logical),(folder,sorted(set(ps)-set(logical)));folderchecks.append({'folder':str(d.relative_to(R)),'files':len(ps),'complete_logical_coverage':True})
assert[r['files']for r in folderchecks]==[154,157,18,4,32,18,2];save('declared-folder-checks.json',folderchecks)
for r in json.loads((P/'immutable-evidence-checks.json').read_text())['folders']:
 d=R/r['folder'];mb=(d/'MANIFEST.json').read_bytes();assert sha(mb)==r['manifest_sha256'];mm=json.loads(mb);rs=mm if isinstance(mm,list)else mm['files']
 for v in rs:
  b=(d/v['path']).read_bytes();assert(len(b),sha(b))==(v['bytes'],v['sha256'])
# Footer must be last paragraph; line wrapping does not alter the required words.
pack=(P/'canonical-pack-r4-draft.md').read_text();last=' '.join(pack.rstrip().split('\n\n')[-1].split());assert last=='**Deliver your findings as a downloadable file named `sg1-dedup-r4-findings.md`** (the findings table and the verdict line, no other wrapping), and also paste its content in your reply.'
after=[{'path':str(q.relative_to(P)),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(P.rglob('*'))if q.is_file()];assert before==after;save('reviewed-folder-after.json',after)
result={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewed_MANIFEST_sha256':sha(manifest),'all173_preparation_files_frozen_exact':True,'logical_inputs':2198,'physical_payloads':1628,'all2198_payloads_restore_exact_candidate':True,'one_administrative_Handoff_rebind_explicit':True,'all570_mappings_complete':True,'all_physical_payloads_used':True,'all50_current_captures_plaintext':True,'all25_ROOT078_exact':True,'all50_Git_blob_ids_reconstructed_without_Git':True,'all1614_old_issued_bundle_byte_exact':True,'old_issued_bytes':nbytes,'old_issued_SHA256':oldhash.hexdigest(),'old40to31_encodings_and3companions_all_exact':True,'all18_current_raw_gzip_Base64_complete':True,'all_complete_current_folders_covered':True,'candidate_bytes':cbytes,'candidate_SHA256':curhash.hexdigest(),'under100MiB':True,'Codex_closing_paragraph_last':True,'reviewed_preparation_unchanged':True,'no_Git_Lean_screen_or_supplied_script_execution':True,'final_records_adoption_render_bindings_remain_root_owned':True};save('peer-validation.json',result);print(json.dumps(result,indent=2))
