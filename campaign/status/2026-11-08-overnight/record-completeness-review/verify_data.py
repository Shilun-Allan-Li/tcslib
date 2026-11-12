from pathlib import Path
import json,hashlib,subprocess,base64,gzip,tarfile,io,datetime,collections
out=Path(__file__).resolve().parent
repo=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
def j(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def dump(name,data):(out/name).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
def git(*args):return subprocess.check_output(['git','-C',str(repo),*args])
paths=j(out/'inputs/ignored-census.json')['ignored_paths'];pre=j(out/'PREPARATION.json');head=pre['records_observed']
# Root-owned commit/index state is sampled read-only; no add/checkout/fetch occurs here.
tree={}
for record in git('ls-tree','-r','-z',head).split(b'\0'):
 if not record:continue
 meta,path=record.split(b'\t',1);tree[path.decode()]=meta.split()[2].decode()
if (out/'inputs/check-ignore-rules.nul.txt').exists():
 rules=(out/'inputs/check-ignore-rules.nul.txt').read_bytes().decode().split('\0');rules=rules[:-1] if rules[-1]=='' else rules
 assert len(rules)==4*58
 rule_rows=[{'ignore_source':rules[i],'line':int(rules[i+1]),'pattern':rules[i+2],'path':rules[i+3]} for i in range(0,len(rules),4)]
 dump('inputs/check-ignore-rules.json',rule_rows);(out/'inputs/check-ignore-rules.nul.txt').unlink()
else:rule_rows=j(out/'inputs/check-ignore-rules.json')
configs=[('FE121','campaign/gates/121-fe-live1-cleanup/review','inputs/FE121.json',None),('current128','campaign/gates/128-ladner-statements/review','inputs/current128.json',None),('prior132','campaign/items/dedup/overnight-2026-11-08/review/ladner-v2','inputs/prior132.json','inputs/prior132-adoption.json'),('prior149','campaign/items/dedup/overnight-2026-11-08/review/ladner-readiness','inputs/prior149.json',None)]
all_rows=[];all_missing=[];all_mismatch=[];not_committed=[];census_matches={}
for label,prefix,manifest_file,adopt in configs:
 manifest=j(out/manifest_file);mapping={r['original_path']:r['records_path'] for r in j(out/adopt)['mapping']} if adopt else {}
 for expected in manifest['files']:
  rel=mapping.get(expected['path'],expected['path'])
  if label=='FE121' and rel.endswith('.lean'):rel+='.txt'
  path=prefix+'/'+rel;source=repo/path
  row={'component':label,'path':path,'manifest_original_path':expected['path'],'expected_bytes':expected['bytes'],'expected_sha256':expected['sha256']}
  if not source.is_file():row['present']=False;all_missing.append(path);all_rows.append(row);continue
  data=source.read_bytes();row.update({'present':True,'actual_bytes':len(data),'actual_sha256':sha(data),'frozen_hash_and_bytes_match':sha(data)==expected['sha256'] and len(data)==expected['bytes'],'Git_blob_if_exact_bytes':blob(data),'committed_at_observed_records':path in tree,'committed_blob_matches_current_full_bytes':tree.get(path)==blob(data)})
  if not row['frozen_hash_and_bytes_match']:all_mismatch.append(path)
  if not row['committed_at_observed_records']:not_committed.append(path)
  all_rows.append(row)
  if path in paths:
   assert row['frozen_hash_and_bytes_match']
   census_matches[path]=row
assert set(census_matches)==set(paths)
assert all((repo/path).is_file() for path in paths)
# The58 data census is complete for current ignored campaign paths at this observation.
ignored=git('ls-files','-o','-i','--exclude-standard','-z','--','campaign').decode().split('\0');ignored=[x for x in ignored if x]
# It is valid for root to have committed the58 while this read-only audit ran.
unexpected_ignored=sorted(set(ignored)-set(paths))
assert not unexpected_ignored
archive_index=j(out/'inputs/FE121-archives.json');archive_receipts=[];recoveries=[]
review='campaign/gates/121-fe-live1-cleanup/review'
for archive in archive_index['archives']:
 phase=archive['phase'];relative=review+'/'+archive['encoded_file'];encoded=(repo/relative).read_bytes()
 assert sha(encoded)==archive['encoded_SHA256'] and tree.get(relative)==blob(encoded)
 committed=git('show',head+':'+relative);assert committed==encoded
 zipped=base64.b64decode(b''.join(encoded.split()),validate=True);assert sha(zipped)==archive['gzip_SHA256']
 tar_bytes=gzip.decompress(zipped);assert sha(tar_bytes)==archive['tar_SHA256']
 expected={r['path']:r for r in archive['members']};actual={};phase_recovered=[]
 with tarfile.open(fileobj=io.BytesIO(tar_bytes),mode='r:') as stream:
  for item in stream.getmembers():
   if item.isdir():continue
   assert item.isfile() and not item.issym() and not item.islnk(),item.name
   assert item.name not in actual and item.name in expected,item.name
   data=stream.extractfile(item).read();member=expected[item.name]
   assert len(data)==member['bytes'] and sha(data)==member['SHA256'],item.name
   actual[item.name]={'bytes':len(data),'sha256':sha(data)}
   canonical=review+'/qa/exports/'+phase+'/'+item.name+('.txt' if item.name.endswith('.lean') else '')
   if canonical in paths:
    raw=(repo/canonical).read_bytes();assert raw==data
    source_pin={'BASE':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','HEAD':'d64dff4fbef865d815c6a561ce8037ea1bae07a2'}[phase]
    original=git('show',source_pin+':'+item.name);assert original==data
    result={'path':canonical,'phase':phase,'archive_member':item.name,'bytes':len(data),'sha256':sha(data),'exact_raw_canonical':True,'exact_frozen_manifest':census_matches[canonical]['frozen_hash_and_bytes_match'],'original_source_commit':source_pin,'original_source_Git_blob':blob(original),'exact_original_pinned_source':True}
    recoveries.append(result);phase_recovered.append(canonical)
 assert set(actual)==set(expected)
 archive_receipts.append({'phase':phase,'committed_encoded_path':relative,'records':head,'encoded_sha256':sha(encoded),'gzip_sha256':sha(zipped),'tar_sha256':sha(tar_bytes),'all_regular_file_members_verified':len(actual),'all_members_exact_to_uncapped_index':True,'recovered_ignored_raw_paths':phase_recovered,'filesystem_extraction_performed':False})
assert len(recoveries)==50 and len({r['path'] for r in recoveries})==50
# Bind8 Mathlib data duplicates also through the original prototype/readiness manifests/maps.
ladner=[census_matches[path] for path in paths if path not in {r['path'] for r in recoveries}];assert len(ladner)==8
assert len({r['actual_sha256'] for r in ladner})==2
extra={path for path in not_committed if path not in paths}
dump('MANIFEST-PAYLOAD-CHECK.json',{'records_observed':head,'components':[{'label':x[0],'prefix':x[1],'manifest_capture':x[2],'optional_ADOPTION_map':x[3]} for x in configs],'full_payload_rows':all_rows,'physical_missing_paths':all_missing,'hash_mismatch_paths':all_mismatch,'not_committed_paths':not_committed,'other_than58_not_committed':sorted(extra),'scope':'All2837+777+132+149 manifest payloads. Original132 path suffix mapping applied; intentional canonical narrative rebases, if any, appear explicitly as mismatches rather than being silently accepted.'})
dump('IGNORED58-VERIFICATION.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records_observed':head,'census_count':58,'all_census_paths_campaign_lean_txt_data':True,'all58_present_and_frozen_hash_exact':True,'full_rows':[census_matches[x] for x in paths],'ignore_rules':rule_rows,'current_ignored_campaign_paths':ignored,'unexpected_other_ignored_paths':unexpected_ignored,'no_source_Git_records_mutation_by_reviewer':True})
dump('ARCHIVE-RECOVERY.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'Strict base64 decode, gzip/tar hashes, read-only in-memory tar members, complete member-index verification and exact comparison to canonical raw, frozen2837 manifest and pinned original source. No extraction or code execution.','actual_archive_receipts':archive_receipts,'all50_ignored_FE121_raw_data_files_exactly_recoverable_from_committed_encoded_inputs':True,'full_recovery_rows':recoveries,'8_Ladner_duplicate_payloads_manifest_bound':ladner,'distinct_Mathlib_payload_sha256s':sorted({r['actual_sha256'] for r in ladner}),'portable_bundle_limit':'The50 raw .claude files are excluded from portable816; full encoded QA archives supply them losslessly. Force-tracking makes the separate full-record-path claim unambiguous; it does not change source or validation.'})
print(json.dumps({'records':head,'ignored58_manifest_matches':len(census_matches),'FE121_archive_recovered':len(recoveries),'all_archive_members_verified':[r['all_regular_file_members_verified'] for r in archive_receipts],'physical_missing_payloads':all_missing,'hash_mismatches':all_mismatch,'not_committed_payload_count':len(not_committed),'other_than58_not_committed':sorted(extra),'unexpected_other_ignored':unexpected_ignored}))
