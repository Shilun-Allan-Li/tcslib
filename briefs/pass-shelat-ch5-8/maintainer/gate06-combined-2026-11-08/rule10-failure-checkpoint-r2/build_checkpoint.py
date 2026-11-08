#!/usr/bin/env python3
"""Own byte-preserving checkpoint writer; source/input programs never execute.

Only this fresh sibling output directory is written. A seekable counting sink
measures exact whole-ZIP size without keeping a duplicate oversized archive.
"""
from pathlib import Path
import csv,datetime,hashlib,io,json,stat,sys,zipfile
sys.dont_write_bytecode=True
ROOT=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
BASE=ROOT/'.lake/ps-maintainer/gate06-combined-20261108'
SOURCE=BASE/'rule10-failure-review-prep-r2'
OUT=BASE/'rule10-failure-checkpoint-r2'
FINAL_SHA='64fcc19bcec224831dfc02368f57e6f53a16f8e0eda3155cbfafb2ba9c443dbb'
LIMIT=50*1024*1024
CHUNK=1<<20

def need(ok,message):
 if not ok:raise RuntimeError(message)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def encode(value):return (json.dumps(value,indent=2,ensure_ascii=False)+'\n').encode()
def identity(s):return (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,stat.S_IMODE(s.st_mode))
def file_digest(path):
 h=hashlib.sha256();n=0
 with path.open('rb') as f:
  while chunk:=f.read(CHUNK):h.update(chunk);n+=len(chunk)
 return n,h.hexdigest()
def write_new(name,raw):
 with (OUT/name).open('xb') as f:f.write(raw)
 return {'path':name,'bytes':len(raw),'sha256':sha(raw)}
def category(rel):
 if rel.startswith('preparation-history/'):return 'PRESERVED_OWN_DRAFT_HISTORY'
 if rel=='FINAL-MANIFEST.json':return 'FROZEN_R2_FINAL_MANIFEST'
 return 'CANONICAL_R2_INDEXED_DATA'
def fingerprint(rows):return sha(''.join(f"{r['path']}\t{r['bytes']}\t{r['sha256']}\n" for r in rows).encode())
def snapshot():
 need(SOURCE.is_dir() and not SOURCE.is_symlink(),'source root not ordinary directory')
 rows=[]
 for p in sorted(SOURCE.rglob('*')):
  s=p.lstat();need(not stat.S_ISLNK(s.st_mode),'input symlink forbidden')
  if stat.S_ISDIR(s.st_mode):continue
  need(stat.S_ISREG(s.st_mode),'nonordinary input')
  rel=p.relative_to(SOURCE).as_posix()
  need(not rel.startswith('/') and all(x not in {'..','.',''} for x in rel.split('/')),'unsafe input relative path')
  need(p.suffix not in {'.olean','.ilean','.zip'},'native object or duplicate archive forbidden')
  n,h=file_digest(p);need(n==s.st_size and identity(p.lstat())==identity(s),'input changed during complete read')
  rows.append({'path':rel,'zip_path':SOURCE.name+'/'+rel,'bytes':n,'sha256':h,'category':category(rel),'stat_identity':identity(s)})
 return rows
def validate_inputs(rows):
 need(len(rows)==4114 and sum(r['bytes'] for r in rows)==346787363,'frozen complete input counts changed')
 by_path={r['path']:r for r in rows};need(by_path['FINAL-MANIFEST.json']['sha256']==FINAL_SHA,'frozen R2 manifest changed')
 manifest=json.loads((SOURCE/'FINAL-MANIFEST.json').read_bytes())
 indexed={r['path']:r for r in manifest['files']}
 need(len(indexed)==len(manifest['files'])==4113 and set(indexed)|{'FINAL-MANIFEST.json'}==set(by_path),'frozen manifest file set differs')
 for name,row in indexed.items():
  need((row['bytes'],row['sha256'])==(by_path[name]['bytes'],by_path[name]['sha256']),'frozen leaf differs '+name)
 report=json.loads((SOURCE/'report.json').read_bytes())
 need(report['R2_source_mappings']['uniquely_mapped_source_comparisons']==114,'source comparison count changed')
 need(report['R2_source_mappings']['unresolved_historical_keys']==[{'file':'TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean','historical_source_key':'TCSlib.Cryptography.GI.unaryMul_poly'}],'unresolved historical case differs')
 need(report['historical_inventory_links']['exact_canonical']==2 and report['historical_inventory_links']['declared_spelling_candidates_not_canonical_identity_or_closure']==146,'exact/candidate link counts changed')
 need(report['future_attacher']['executed'] is False and report['waiver'] is False and report['merge_clearance'] is False,'no attacher execution/waiver/acceptance')

class CountingSink:
 """Seekable write-only byte extent counter; stores no archive/input bytes."""
 def __init__(self):self.pos=0;self.extent=0
 def tell(self):return self.pos
 def write(self,data):
  self.pos+=len(data);self.extent=max(self.extent,self.pos);return len(data)
 def seek(self,offset,whence=0):
  if whence==0:self.pos=offset
  elif whence==1:self.pos+=offset
  elif whence==2:self.pos=self.extent+offset
  else:raise ValueError('bad seek mode')
  need(self.pos>=0,'negative counting sink position');return self.pos
 def flush(self):pass
 def seekable(self):return True

def fill_zip(target,rows):
 with zipfile.ZipFile(target,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9,allowZip64=True) as z:
  for row in rows:
   p=SOURCE/row['path'];need(identity(p.lstat())==tuple(row['stat_identity']),'input changed before ZIP stream')
   info=zipfile.ZipInfo(row['zip_path'],date_time=(1980,1,1,0,0,0))
   info.compress_type=zipfile.ZIP_DEFLATED;info._compresslevel=9;info.create_system=3
   info.external_attr=(stat.S_IFREG|row['stat_identity'][4])<<16
   h=hashlib.sha256();n=0
   with p.open('rb') as source,z.open(info,'w',force_zip64=True) as archived:
    while chunk:=source.read(CHUNK):h.update(chunk);n+=len(chunk);archived.write(chunk)
   need((n,h.hexdigest())==(row['bytes'],row['sha256']) and identity(p.lstat())==tuple(row['stat_identity']),'input changed during ZIP stream')
def measure(rows):
 sink=CountingSink();fill_zip(sink,rows);return sink.extent
def readback(path,rows):
 expected={r['zip_path']:r for r in rows}
 with zipfile.ZipFile(path) as z:
  infos=z.infolist()
  need(len(infos)==len(expected) and {i.filename for i in infos}==set(expected),'archive has missing/duplicate entries')
  for info in infos:
   row=expected[info.filename]
   need(not info.is_dir() and not(info.flag_bits&1) and stat.S_ISREG(info.external_attr>>16),'bad ZIP type/encryption')
   h=hashlib.sha256();n=0
   with z.open(info) as f:
    while chunk:=f.read(CHUNK):h.update(chunk);n+=len(chunk)
   need((n,h.hexdigest())==(row['bytes'],row['sha256']) and n==info.file_size,'complete ZIP readback differs')

def main():
 need(OUT.resolve().parent==BASE.resolve() and not OUT.resolve().is_relative_to(SOURCE.resolve()),'output must be separate sibling')
 need(set(p.name for p in OUT.iterdir())=={'build_checkpoint.py'},'fresh checkpoint directory required')
 started=datetime.datetime.now(datetime.timezone.utc).isoformat();before=snapshot();validate_inputs(before)
 full_size=measure(before)
 if full_size<=LIMIT:
  selected=[('rule10-failure-review-prep-r2.zip',before,full_size)]
  strategy='ONE_COMPLETE_ZIP'
 else:
  canonical=[r for r in before if r['category']!='PRESERVED_OWN_DRAFT_HISTORY']
  history=[r for r in before if r['category']=='PRESERVED_OWN_DRAFT_HISTORY']
  selected=[('rule10-failure-review-prep-r2-canonical.zip',canonical,measure(canonical)),
            ('rule10-failure-review-prep-r2-history.zip',history,measure(history))]
  strategy='CANONICAL_AND_HISTORY_SPLIT_NO_EXCLUSIONS'
 need(all(n<=LIMIT for _,_,n in selected),'selected archive exceeds50MiB; preserve inputs and report')
 union=[r['path'] for _,rs,_ in selected for r in rs]
 need(len(union)==len(before) and set(union)=={r['path'] for r in before},'archive union drops or duplicates source files')
 archives=[];location={}
 for name,rows,expected_size in selected:
  p=OUT/name
  with p.open('xb') as f:fill_zip(f,rows)
  need(p.stat().st_size==expected_size,'actual ZIP size differs from exact counting pass')
  readback(p,rows);n,h=file_digest(p)
  archives.append({'path':name,'bytes':n,'sha256':h,'entries':len(rows),'uncompressed_bytes':sum(r['bytes'] for r in rows)})
  for row in rows:need(row['path'] not in location,'duplicate union path');location[row['path']]=name
 after=snapshot();need(before==after,'frozen inputs changed between complete before/after reads');validate_inputs(after)
 public=[{k:v for k,v in r.items() if k!='stat_identity'}|{'archive':location[r['path']]} for r in before]
 categories={c:{'files':sum(r['category']==c for r in before),'bytes':sum(r['bytes'] for r in before if r['category']==c)} for c in sorted({r['category'] for r in before})}
 indices=[write_new('FILES.json',encode({'source_root':str(SOURCE),'files':public,'categories':categories}))]
 buf=io.StringIO();writer=csv.writer(buf,delimiter='\t',lineterminator='\n')
 keys=['path','archive','zip_path','bytes','sha256','category'];writer.writerow(keys)
 for row in public:writer.writerow([row[k] for k in keys])
 indices.append(write_new('FILES.tsv',buf.getvalue().encode()))
 builder_sha=sha(Path(__file__).read_bytes())
 selection={'strategy':strategy,'single_zip_measured_exact_bytes':full_size,'per_archive_limit_bytes':LIMIT,'per_archive_limit_units':'50MiB','size_counting_pass_retained_no_duplicate_archive':True}
 facts={'source_comparisons_lexical_only':114,'unresolved_historical_keys':['TCSlib.Cryptography.GI.unaryMul_poly'],'exact_canonical_inventory_links':2,'declared_spelling_candidates_not_identity_or_closure':146,'historical_root_keys':115,'historical_head_diagnostics':145,'historical_base_source_diagnostics':7,'original_recorded_raw_ranges_preserved_not_identity':230,'waiver':False}
 manifest={'status':'FROZEN_R2_ARCHIVAL_CHECKPOINT_NO_ACCEPTANCE','source_root':str(SOURCE),'source_final_manifest_sha256':FINAL_SHA,
  'head':'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37','actual_PRbase':'067c5d8d6dd436e62681d7dc607984c705dc80a2',
  'archives':archives,'archive_selection':selection,'complete_union_entries':len(before),'complete_union_uncompressed_bytes':sum(r['bytes'] for r in before),
  'categories':categories,'indices':indices,'source_content_fingerprint_sha256':fingerprint(before),'builder_sha256':builder_sha,
  'facts_preserved_without_acceptance':facts,'all_original_bytes_unchanged':True,'every_selected_archive_fully_read_back':True,
  'archive_includes_itself':False,'R1_archive_included':False,'native_run':False,'input_programs_executed':False,'attacher_executed':False,
  'limits':['All canonical R2 indexed files, frozen R2 final manifest and preserved own draft history are included without exclusions.',
   'No encoding/newline normalization; files are archived as exact bytes. Drafts remain historical data, not current claims.',
   'This checkpoint grants no inheritance/waiver/pass/acceptance or current native outcome claim.','All actual failures and the one unresolved lexical case remain review-required.']}
 mr=write_new('checkpoint-manifest.json',encode(manifest))
 receipt={'status':'COMPLETE_UNION_READBACK_AND_FROZEN_INPUTS_VERIFIED_NO_ACCEPTANCE','started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'archives':archives,'checkpoint_manifest':mr,'archive_selection':selection,'source_before_fingerprint_sha256':fingerprint(before),'source_after_fingerprint_sha256':fingerprint(after),
  'full_source_before_after_equal':True,'complete_union_entries':len(before),'zip_entries_fully_read_back':sum(a['entries'] for a in archives),
  'complete_union_uncompressed_bytes':sum(r['bytes'] for r in before),'categories':categories,'facts_preserved_without_acceptance':facts,
  'originals_preserved':True,'native_run':False,'input_programs_executed':False,'attacher_executed':False,'builder_sha256':builder_sha}
 rr=write_new('checkpoint-receipt.json',encode(receipt))
 sums=[{'path':'build_checkpoint.py','sha256':builder_sha},*archives,*indices,mr,rr]
 write_new('SHA256SUMS',''.join(f"{r['sha256']}  {r['path']}\n" for r in sums).encode())
 print(json.dumps({'archives':archives,'strategy':strategy,'single_zip_exact_bytes':full_size,'manifest_sha256':mr['sha256'],'receipt_sha256':rr['sha256'],'union_files':len(before),'union_uncompressed_bytes':sum(r['bytes'] for r in before),'categories':categories,'source_unchanged':True,'native_or_acceptance_claim':False},indent=2))

if __name__=='__main__':main()
