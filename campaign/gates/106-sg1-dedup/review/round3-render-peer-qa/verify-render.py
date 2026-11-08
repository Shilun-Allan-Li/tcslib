from pathlib import Path
import base64,codecs,datetime,gzip,hashlib,io,json,os,struct,subprocess,sys
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent
C=json.loads((OUT/'context.json').read_text());ROOT=Path(C['root']);STAGE=Path(C['stage']);EXCHANGE=Path(C['exchange']);G='campaign/gates/106-sg1-dedup';source=C['source'];records=C['records'];sha=lambda b:hashlib.sha256(b).hexdigest()
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE).stdout
batch=subprocess.Popen(['git','-C',str(ROOT),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
def blob(pin,path):
 batch.stdin.write((pin+':'+path+'\n').encode());batch.stdin.flush();head=batch.stdout.readline().decode().strip().split();assert len(head)==3 and head[1]=='blob',(pin,path,head)
 oid,kind,size=head;size=int(size);data=batch.stdout.read(size);assert len(data)==size and batch.stdout.read(1)==b'\n';assert hashlib.sha1(b'blob '+str(size).encode()+b'\0'+data).hexdigest()==oid
 return oid,data
try:
 order_oid,order_raw=blob(records,C['canonical_order']);paths=[x.strip() for x in order_raw.decode('utf-8').splitlines() if x.strip()];assert len(paths)==len(set(paths))==C['expected_sections'];assert paths[0]==G+'/pack-r3.md';pathset=set(paths)
 assert order_raw==(STAGE/'BUNDLE-FILES.txt').read_bytes()==(EXCHANGE/'BUNDLE-FILES.txt').read_bytes()
 tool_oid,tool=blob(records,'devtools/seyoon/mkbundle-mixed.py');assert tool==(ROOT/'devtools/seyoon/mkbundle-mixed.py').read_bytes();assert b"return lrev if p.startswith('TCSlib/') else orev" in tool
 bundle=STAGE/C['bundle'];initial=bundle.stat();whole=hashlib.sha256();sections=[];json_count=0
 with bundle.open('rb') as f:
  def expected(data):
   got=f.read(len(data));assert got==data,('rendered byte mismatch',len(sections),paths[len(sections)],f.tell()-len(data));whole.update(got)
  for number,path in enumerate(paths):
   pin=source if path.startswith('TCSlib/') else records;oid,data=blob(pin,path);text=data.decode('utf-8',errors='strict')
   if path.endswith('.json'):json.loads(text);json_count+=1
   content=data+(b'' if data.endswith(b'\n') else b'\n');fenced=path.endswith('.lean') or path.endswith('.py');body=(b'```\n'+content+b'```\n') if fenced else content
   if number:expected(b'\n')
   start=f.tell();header=('## ===== '+path+' =====\n\n').encode('utf-8');expected(header);body_start=f.tell();expected(body)
   sections.append(dict(number=number+1,path=path,pin=pin,blob=oid,bytes=len(data),sha256=sha(data),rendered_body_bytes=len(body),rendered_body_sha256=sha(body),section_start=start,body_start=body_start,section_end=f.tell(),fenced=fenced,terminal_newline_added=not data.endswith(b'\n')))
  assert f.read(1)==b''
 bundle_hash=whole.hexdigest();assert bundle.stat().st_size==initial.st_size and bundle.stat().st_mtime_ns==initial.st_mtime_ns;assert initial.st_size<C['hosting_limit_bytes']
 index={x['path']:x for x in sections};save('independent-section-index.json',sections)
 print('ALL RENDERED SECTIONS PASS '+str(len(sections))+'; bytes '+str(initial.st_size)+'; SHA '+bundle_hash,flush=True)
 # Check the separately published root index only AFTER independent section reconstruction.
 published=json.loads((EXCHANGE/'INPUT-INDEX.json').read_text());assert (published['source'],published['records'],published['sections'],published['bundle_bytes'],published['bundle_sha256'])==(source,records,len(paths),initial.st_size,bundle_hash);assert published['JSON_parsed']==json_count
 for own,theirs in zip(sections,published['files']):
  assert {k:own[k] for k in theirs}==theirs,(own['path'],'published index differs')
 assert len(published['files'])==len(sections)
 enc_path=G+'/review/round3-final-packet/encoding-receipt.json';_,b=blob(records,enc_path);enc=json.loads(b);transforms=enc['transforms'];assert len(transforms)==40 and len({x['encoding_path'] for x in transforms})==31;aliases={x['original']['path']:x['encoding_path'] for x in transforms};assert len(aliases)==40
 alias_results=[]
 for row in transforms:
  original=row['original'];ep=row['encoding_path'];assert ep in pathset and original['path'] not in pathset
  _,encoded=blob(records,ep);encoded.decode('ascii',errors='strict');assert (len(encoded),sha(encoded))==(row['encoded_utf8_bytes'],row['encoded_utf8_sha256'])
  compressed=base64.b64decode(b''.join(encoded.split()),validate=True);assert (len(compressed),sha(compressed))==(row['gzip_bytes'],row['gzip_sha256']);assert compressed[:3]==b'\x1f\x8b\x08' and compressed[3]&8==0 and compressed[4:8]==b'\0\0\0\0'
  raw=gzip.decompress(compressed);raw.decode('utf-8',errors='strict');assert (len(raw),sha(raw))==(original['bytes'],original['sha256']);oid,git_raw=blob(records,original['path']);assert raw==git_raw
  alias_results.append(dict(original=original['path'],original_blob=oid,raw_bytes=len(raw),raw_sha256=sha(raw),encoding_path=ep,gzip_bytes=len(compressed),gzip_sha256=sha(compressed),encoded_utf8_bytes=len(encoded),encoded_utf8_sha256=sha(encoded),rendered_section_exact=True,full_roundtrip_and_records_Git_bytes_equal=True))
 for row in enc['binary_gzip_equivalents']:
  assert row['represented_by'] in pathset and row['path'] not in pathset
  _,coded=blob(records,row['represented_by']);decoded=base64.b64decode(b''.join(coded.split()),validate=True);oid,raw=blob(records,row['path']);assert decoded==raw and (len(raw),sha(raw))==(row['bytes'],row['sha256'])
  alias_results.append(dict(original=row['path'],original_blob=oid,encoding_path=row['represented_by'],raw_bytes=len(raw),raw_sha256=sha(raw),kind='existing binary gzip companion',full_roundtrip_and_records_Git_bytes_equal=True))
 save('lossless-alias-verification.json',dict(substituted_originals=40,distinct_encoded_sections=31,binary_gzip_companions=3,all43_mappings=alias_results,all_rendered=True,no_source50_aliases=True))
 print('ALL40→31 ALIASES +3 BINARY COMPANIONS PASS',flush=True)
 # Current plaintext captures are stored at records pin, and independently equal source/base blobs.
 home=G+'/review/round3-current-source-screen25-final79';_,raw=blob(records,home+'/capture.json');capture=json.loads(raw);base=capture['base'];assert capture['head']==source and len(capture['population'])==len(set(capture['population']))==25
 source_rows=[]
 for side in ['base','head']:
  assert len(capture['sides'][side]['files'])==25
  for row in capture['sides'][side]['files']:
   p=home+'/inputs/'+side+'/'+row['path']+'.txt';assert p in pathset and p not in aliases and not index[p]['fenced'];pin=capture[side];oid,data=blob(pin,row['path']);record_oid,copied=blob(records,p);assert data==copied and oid==row['blob']==record_oid and (len(data),sha(data))==(row['bytes'],row['sha256']);assert index[p]['pin']==records and index[p]['blob']==record_oid
   source_rows.append(dict(capture_path=p,storage_pin=records,source_pin=pin,source_path=row['path'],source_and_capture_blob=oid,bytes=len(data),sha256=sha(data),plaintext_rendered_exact=True))
 assert len(source_rows)==50;save('source50-plaintext-verification.json',source_rows)
 _,raw=blob(records,G+'/review/round3-root-adoption/mixed-pin-rebinding.json');rebind=json.loads(raw);assert rebind['source']==source and len(rebind['corrected_paths'])==5
 corrections=[]
 for row in rebind['corrected_paths']:
  p=row['path'];a=index[p];current=row['actual_final_mixed_pin_binding'];historical=row['frozen_inventory_binding'];assert a['pin']==source and (a['bytes'],a['sha256'])==(current['bytes'],current['sha256']);_,old=blob(historical['pin'],p);assert (len(old),sha(old))==(historical['bytes'],historical['sha256']);assert historical['pin']==base
  corrections.append(dict(path=p,actual_final_pin=a['pin'],actual_blob=a['blob'],actual_sha256=a['sha256'],historical_inventory_pin=historical['pin'],historical_inventory_sha256=historical['sha256'],both_current_and_baseline_captures_present=True))
 save('five-source-binding-verification.json',corrections)
 # Preserve complete earlier selections and declared whole-folder scopes; no recursive QA demand.
 _,raw=blob(records,G+'/review/round3-publication-supplement/BUNDLE-FILES-r3-draft.txt');draft=raw.decode().splitlines();_,raw=blob(records,G+'/review/round3-final-packet/BUNDLE-FILES-candidate.txt');candidate=raw.decode().splitlines();assert len(draft)==1609 and len(candidate)==1539 and paths[:1609]==draft
 assert [p for p in paths if p in set(candidate)]==candidate
 _,raw=blob(records,G+'/review/round3-final-packet/QA.json');frozen=json.loads(raw);folders=[x['folder'] for x in frozen['complete_folder_coverage']]
 folders += [G+'/review/round3-final-packet-peer-review',G+'/review/round3-publication-supplement',G+'/review/round3-root-adoption']
 _,raw=blob(records,G+'/review/round3-publication-supplement/context-rebinding.json');context_changes=json.loads(raw)
 coverage=[]
 for folder in folders:
  names=git('ls-tree','-r','--name-only',records,'--',folder).decode().splitlines();missing=[p for p in names if p not in pathset and p not in aliases and p not in {x['path'] for x in enc['binary_gzip_equivalents']}];assert not missing,(folder,missing)
  coverage.append(dict(folder=folder,all_Git_files=len(names),direct=sum(p in pathset for p in names),lossless_alias=sum(p in aliases or p in {x['path'] for x in enc['binary_gzip_equivalents']} for p in names),complete=True))
 save('scope-and-order-verification.json',dict(canonical_sections=len(paths),draft1609_exact_prefix=True,candidate1539_all_preserved_in_order=True,root_added_five_paths=paths[1609:],all50_sources_plaintext=True,folder_coverage=coverage,post_bundle_own_peerQA_intentionally_not_required=True))
 # Frozen external inventory is historical; record its full differences from actual rendered bindings.
 _,raw=blob(records,G+'/review/round3-publication-supplement/external-input-inventory.json');prior=json.loads(raw);deltas=[]
 for row in prior['files']:
  a=index[row['path']]
  if (row['bytes'],row['sha256'])!=(a['bytes'],a['sha256']):deltas.append(dict(path=row['path'],historical_bytes=row['bytes'],historical_sha256=row['sha256'],actual_pin=a['pin'],actual_bytes=a['bytes'],actual_sha256=a['sha256'],kind='corrected source proof pin' if row['path'].startswith('TCSlib/') else 'canonical current records context / adopted pack'))
 assert {x['path'] for x in deltas if x['path'].startswith('TCSlib/')}=={x['path'] for x in corrections};save('historical-inventory-rendered-differences.json',dict(frozen_inventory_rows=len(prior['files']),observed_records_commit=prior['observed_records_commit'],current_records_pin=records,all_differences=deltas,authority='Actual mixed-pin Git blobs and canonical current pack govern. Frozen candidate/draft inventories retain their actual historical hashes; no backward mutation or source50 substitution.'))
 # Graph provenance dependency is actual rendered bytes, without executing it.
 _,graph=blob(records,'devtools/seyoon/graph.py');_,copy=blob(records,G+'/review/round3-publication-supplement/graph.py.txt');assert graph==copy and len(graph)==4784 and sha(graph)=='c4c1aa599a091c88f77062fd2fca4482ed8017e683819a650e343760ac78d72c'
 # Final exchange/stage identity and complete four-file checksum coverage.
 listed={}
 for line in (EXCHANGE/'SHA256SUMS').read_text().splitlines():
  digest,name=line.split('  ',1);assert name not in listed;data=(EXCHANGE/name).read_bytes();assert sha(data)==digest;listed[name]=digest
 assert set(listed)=={C['bundle'],'README.md','BUNDLE-FILES.txt','INPUT-INDEX.json'} and listed[C['bundle']]==bundle_hash
 assert sha((EXCHANGE/C['bundle']).read_bytes())==bundle_hash and (EXCHANGE/C['bundle']).stat().st_size==initial.st_size
 readme=(EXCHANGE/'README.md').read_text();assert all(x in readme for x in [source,records,str(len(paths)),str(initial.st_size),bundle_hash]);assert 'historical' in readme and 'Not yet dispatched' in readme
 assert bundle.stat().st_size==initial.st_size and bundle.stat().st_mtime_ns==initial.st_mtime_ns
 result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),result='PASS bounded independent mixed-pin rendered publication QA',source=source,records=records,sections=len(sections),JSON_sections_parsed=json_count,bundle_bytes=initial.st_size,bundle_sha256=bundle_hash,all_rendered_sections_exact_Git_blobs=True,correct_TCSlib_source_pin=True,other_sections_records_pin=True,current_source50_plaintext_exact=True,five_historical_wrong_root_bindings_corrected=True,aliases_40_originals_31_encodings_verified=True,binary_companions_3_verified=True,all_original1539_and_draft1609_sections_retained_in_order=True,declared_complete_folders_verified=len(coverage),graph_dependency_exact=True,co_published_index_exact=True,exchange_stage_body_identical=True,all_four_exchange_checksums_verified=True,hosting_limit_bytes=C['hosting_limit_bytes'],hosting_margin_bytes=C['hosting_limit_bytes']-initial.st_size,all_rendered_sections_UTF8=True,no_numerical_Lean_screen_or_sweep_reruns=True,no_stage_exchange_canonical_frozen_or_Git_mutation=True,own_QA_postdates_packet_and_not_recursively_required=True,canonical_context_current_frozen_inventories_historical=True,historical_external_inventory_differences=len(deltas))
 save('QA.json',result);print(json.dumps(result,indent=2),flush=True)
finally:
 batch.stdin.close();batch.stdout.close();batch.wait();assert batch.returncode==0
