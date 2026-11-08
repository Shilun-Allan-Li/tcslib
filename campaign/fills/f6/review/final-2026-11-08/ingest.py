"""Maintainer-owned safe data ingestion. No delivered script or Lean execution."""
from pathlib import Path,PurePosixPath
import datetime,hashlib,json,os,re,stat,tempfile,unicodedata,zipfile
out=Path(__file__).resolve().parent
exchange=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange/arora-barak-ch3-4/inbox/fill-f6')
scratch=Path(tempfile.mkdtemp(prefix='tcslib-f6-review-',dir='/private/tmp'));os.chmod(scratch,0o700)
H=lambda b:hashlib.sha256(b).hexdigest()
rows=[];inventories=[];checkmaps=[]
for label in ['cp01','cp02','final']:
 f=exchange/f'fill-f6-{label}.zip';raw=f.read_bytes();status=exchange/f'fill-f6-{label}-STATUS.md'
 st=status.read_bytes();assert H(raw) in st.decode() and str(len(raw)) in st.decode()
 prefix=f'fill-f6-{label}/';dest=scratch/label;dest.mkdir(mode=0o700);entries=[];names=set();folds=set();total=0;contents={}
 with zipfile.ZipFile(f) as z:
  for i in z.infolist():
   name=i.filename;pp=PurePosixPath(name);key=unicodedata.normalize('NFC',name.rstrip('/')).casefold()
   assert name.startswith(prefix) and name and not pp.is_absolute() and '..' not in pp.parts
   assert '\\' not in name and not any(c in name for c in '\x00\r\n\t') and len(name)<4096
   assert name not in names and key not in folds;names.add(name);folds.add(key)
   mode=i.external_attr>>16;assert stat.S_IFMT(mode) in [0,stat.S_IFREG,stat.S_IFDIR] and not i.flag_bits&1
   assert 0<=i.file_size<=64*1024*1024;total+=i.file_size;assert total<=256*1024*1024
   data=z.read(i);assert len(data)==i.file_size
   rel=name[len(prefix):];target=dest/rel
   if i.is_dir():target.mkdir(parents=True,exist_ok=True)
   else:
    assert rel and not target.exists()
    target=target.with_name(target.name+'.txt') if target.suffix=='.lean' else target
    assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);contents[rel]=data
   entries.append({'zip_name':name,'directory':i.is_dir(),'bytes':i.file_size,'compressed_bytes':i.compress_size,'crc32':f'{i.CRC:08x}','sha256':None if i.is_dir() else H(data),'inert_scratch_path':str(target)})
  assert z.testzip() is None
 manifest=json.loads(contents['MANIFEST.json']);mr=manifest['files'];mp={r['path']:r for r in mr};assert len(mp)==len(mr)
 assert set(mp)==set(contents)-{'MANIFEST.json','SHA256SUMS'}
 checks=[]
 for path,r in mp.items():
  data=contents[path];assert (len(data),H(data))==(r['bytes'],r['sha256']);checks.append({'path':path,'bytes':len(data),'sha256':H(data),'manifest_PASS':True})
 sums={}
 for line in contents['SHA256SUMS'].decode().splitlines():
  m=re.fullmatch(r'([0-9a-f]{64})  \./(.+)',line);assert m,line;sha,path=m.groups();assert path not in sums;sums[path]=sha;assert H(contents[path])==sha
 assert set(sums)==set(contents)-{'SHA256SUMS'}
 assert contents['BASE.txt'].decode().strip()=='3023dc1408c3d216fc07a7cbba9ae30135b861ed'
 assert manifest['proof_base']=='3023dc1408c3d216fc07a7cbba9ae30135b861ed' and manifest['records_commit']=='f41bdaea207724606d8934bfc2c9a823c5dd1e2f'
 assert manifest['bundle_sha256']=='8fa482702846898f7fa04c4e1b0aa012300b4febaa6385ee8caa869cf14740be' and manifest['bundle_sections']==624
 assert contents['HEAD.txt'].decode().strip()==manifest['head']
 src=contents['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']
 (out/f'{label}-Hierarchy.lean.txt').write_bytes(src)
 for name in ['REPORT.md','PRIVATE-HELPERS.md','ADMISSIONS.md','COMMITS.txt','BASE.txt','HEAD.txt','SOURCE-SHA256.txt']:
  if name in contents:(out/f'{label}-{name}.received.txt').write_bytes(contents[name])
 (out/f'{label}-STATUS.received.md').write_bytes(st)
 inventories.append({'label':label,'entries':entries})
 checkmaps.append({'label':label,'manifest_entries':checks,'SHA256SUMS':sums})
 rows.append({'label':label,'source_zip':str(f),'zip_bytes':len(raw),'zip_sha256':H(raw),'status_bytes':len(st),'status_sha256':H(st),'zip_entries':len(entries),'regular_payload_files':len(contents),'manifest_entries':len(mr),'SHA256SUMS_entries':len(sums),'uncompressed_bytes':total,'all_manifest_and_checksums_and_CRC_PASS':True,'head_as_supplied':manifest['head'],'owned_source_bytes':len(src),'owned_source_sha256':H(src),'extracted_inert_root':str(dest)})
(out/'zip-inventory.json').write_text(json.dumps(inventories,indent=2)+'\n')
(out/'all-checksum-verification.json').write_text(json.dumps(checkmaps,indent=2)+'\n')
receipt={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'All three ZIPs safely inventoried and CRC/SHA manifest-checked in private fresh scratch; no delivered script/Lean executed; raw originals read-only. All .lean files renamed .lean.txt.','scratch_root':str(scratch),'zip_guards':{'unique_NFC_casefold_paths':True,'relative_paths_no_dotdot_backslash_control_char':True,'no_symlink_special_or_encrypted_entry':True,'per_file_max_bytes':64*1024*1024,'per_zip_max_expanded_bytes':256*1024*1024,'no_source_tree_extraction':True},'deliveries':rows,'no_Lean_screen_Git_source_cache_snapshot_commit_push_action':True}
(out/'ingestion.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'scratch':str(scratch),'deliveries':rows},indent=2))
