#!/usr/bin/env python3
"""Own checkpoint writer. Reads source artifacts as opaque bytes; executes none.

Only the fresh sibling checkpoint directory is written. No Lean/Git/cache/native
commands or imports of received/source helpers. Originals remain byte-identical.
"""
from pathlib import Path
from collections import Counter
import ast,csv,datetime,hashlib,io,json,os,stat,sys,zipfile
sys.dont_write_bytecode=True
ROOT=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
BASE=ROOT/'.lake/ps-maintainer/gate06-combined-20261108'
SOURCE=BASE/'rule10-failure-review-prep-r1'
OUT=BASE/'rule10-failure-checkpoint-r1'
EXPECTED_FINAL='7a3a7dfc28bf29310271310da1541b1fdf20860d04968d5dd7a296c983030d42'
EXPECTED_FILES=2725
EXPECTED_BYTES=203859547
CHUNK=1<<20

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def encoded(x):return (json.dumps(x,indent=2,ensure_ascii=False)+'\n').encode()
def write_new(name,raw):
 p=OUT/name
 with p.open('xb') as f:f.write(raw)
 return {'path':name,'bytes':len(raw),'sha256':sha(raw)}
def fingerprint(rows):return sha(''.join(f"{r['path']}\t{r['bytes']}\t{r['sha256']}\n" for r in rows).encode())
def category(path):
 if path.parts[0]=='preflight-draft-1':return 'PRESERVED_EARLIER_DRAFT_HISTORY'
 if '__pycache__' in path.parts:return 'PREEXISTING_PYTHON_BYTECODE_DATA_NOT_EXECUTED'
 return 'FROZEN_CANONICAL_PREPARATION'
def identity(s):return (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,stat.S_IMODE(s.st_mode))
def full_snapshot():
 need(SOURCE.is_dir() and not SOURCE.is_symlink(),'source root is not ordinary directory')
 rows=[]
 for path in sorted(SOURCE.rglob('*')):
  s=path.lstat();need(not stat.S_ISLNK(s.st_mode),'source symlink is forbidden')
  if stat.S_ISDIR(s.st_mode):continue
  need(stat.S_ISREG(s.st_mode),'nonordinary source file')
  rel=path.relative_to(SOURCE);need(not rel.is_absolute() and all(p not in ('','..','.') for p in rel.parts),'unsafe relative path')
  need(path.suffix not in {'.olean','.ilean'},'unexpected native object in source preparation')
  h=hashlib.sha256();n=0
  with path.open('rb') as f:
   while chunk:=f.read(CHUNK):h.update(chunk);n+=len(chunk)
  need(identity(path.lstat())==identity(s) and n==s.st_size,'source changed during full read')
  rows.append({'path':rel.as_posix(),'bytes':n,'sha256':h.hexdigest(),'category':category(rel),'stat_identity':identity(s)})
 return rows

def main():
 need(OUT.resolve().parent==BASE.resolve() and not OUT.resolve().is_relative_to(SOURCE.resolve()),'checkpoint must be outside source')
 expected_outputs=['rule10-failure-review-prep-r1.zip','FILES.json','FILES.tsv','checkpoint-manifest.json','checkpoint-receipt.json','SHA256SUMS']
 need(all(not(OUT/n).exists() for n in expected_outputs),'checkpoint output already exists; never overwrite')
 need(sha((SOURCE/'FINAL-MANIFEST.json').read_bytes())==EXPECTED_FINAL,'frozen preparation manifest changed')
 started=datetime.datetime.now(datetime.timezone.utc).isoformat();before=full_snapshot()
 need(len(before)==EXPECTED_FILES and sum(r['bytes'] for r in before)==EXPECTED_BYTES,'full source counts differ from announced frozen checkpoint')
 archive=OUT/expected_outputs[0]
 with archive.open('xb') as rawout:
  with zipfile.ZipFile(rawout,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6,allowZip64=True) as z:
   for row in before:
    path=SOURCE/row['path'];need(identity(path.lstat())==tuple(row['stat_identity']),'source stat changed before ZIP write')
    info=zipfile.ZipInfo(SOURCE.name+'/'+row['path'],date_time=(1980,1,1,0,0,0))
    info.compress_type=zipfile.ZIP_DEFLATED;info.create_system=3;info.external_attr=(stat.S_IFREG|row['stat_identity'][4])<<16
    h=hashlib.sha256();n=0
    with path.open('rb') as incoming,z.open(info,'w',force_zip64=True) as target:
     while chunk:=incoming.read(CHUNK):h.update(chunk);n+=len(chunk);target.write(chunk)
    need(h.hexdigest()==row['sha256'] and n==row['bytes'] and identity(path.lstat())==tuple(row['stat_identity']),'source changed while archived')
 # Complete archive readback, including ZIP CRC verification and exact entry set.
 with zipfile.ZipFile(archive,'r') as z:
  infos=z.infolist();need(len(infos)==len(before) and len({i.filename for i in infos})==len(before),'ZIP duplicate/missing entries')
  expected={SOURCE.name+'/'+r['path']:r for r in before};need(set(expected)=={i.filename for i in infos},'ZIP entry set differs')
  for info in infos:
   row=expected[info.filename];need(not info.is_dir() and info.file_size==row['bytes'] and not(info.flag_bits&1),'bad ZIP entry type/size/encryption')
   need(stat.S_ISREG(info.external_attr>>16),'ZIP nonordinary entry')
   h=hashlib.sha256();n=0
   with z.open(info,'r') as f:
    while chunk:=f.read(CHUNK):h.update(chunk);n+=len(chunk)
   need(h.hexdigest()==row['sha256'] and n==row['bytes'],'ZIP full readback mismatch')
 after=full_snapshot();need(before==after,'source changed between before/after complete reads')
 need(sha((SOURCE/'FINAL-MANIFEST.json').read_bytes())==EXPECTED_FINAL,'frozen preparation manifest changed after readback')
 h=hashlib.sha256()
 with archive.open('rb') as f:
  while chunk:=f.read(CHUNK):h.update(chunk)
 archive_row={'path':archive.name,'sha256':h.hexdigest(),'bytes':archive.stat().st_size,'entries':len(before),'uncompressed_bytes':sum(r['bytes'] for r in before)}
 public=[{k:v for k,v in r.items() if k!='stat_identity'}|{'zip_path':SOURCE.name+'/'+r['path']} for r in before]
 categories={c:{'files':sum(r['category']==c for r in before),'bytes':sum(r['bytes'] for r in before if r['category']==c)} for c in sorted({r['category'] for r in before})}
 indices=[];indices.append(write_new('FILES.json',encoded({'source_root':str(SOURCE),'files':public,'categories':categories})))
 buf=io.StringIO();w=csv.writer(buf,delimiter='\t',lineterminator='\n');w.writerow(['path','zip_path','bytes','sha256','category'])
 for r in public:w.writerow([r[k] for k in ['path','zip_path','bytes','sha256','category']])
 indices.append(write_new('FILES.tsv',buf.getvalue().encode()))
 builder=Path(__file__).read_bytes()
 manifest={'status':'FROZEN_NONNATIVE_CHECKPOINT_NO_ACCEPTANCE','source_root':str(SOURCE),'source_final_manifest_sha256':EXPECTED_FINAL,
  'source_head':'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37','actual_PRbase':'067c5d8d6dd436e62681d7dc607984c705dc80a2',
  'archive':archive_row,'categories':categories,'indices':indices,'source_content_fingerprint_sha256':fingerprint(before),
  'builder_sha256':sha(builder),'archive_prefix':SOURCE.name+'/',
  'archive_includes_itself':False,'all_original_source_bytes_unchanged':True,'full_archive_readback_verified':True,
  'limits':['Current59 native outcomes remain unknown; no inheritance/waiver/pass/acceptance claim.',
   'Canonical preparation, prior draft history and preexisting Python bytecode are explicitly distinguished.',
   'Every included input is archived as opaque bytes; no input/source helper or bytecode was executed.',
   'No .olean/.ilean included; no Lean/native/cache/build/Git/app commands performed.']}
 mr=write_new('checkpoint-manifest.json',encoded(manifest))
 receipt={'status':'ARCHIVE_AND_COMPLETE_READBACK_VERIFIED_NO_ACCEPTANCE','started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
  'archive':archive_row,'checkpoint_manifest':mr,'source_before_fingerprint_sha256':fingerprint(before),'source_after_fingerprint_sha256':fingerprint(after),
  'full_source_before_after_equal':True,'full_source_file_count':len(before),'full_source_bytes':sum(r['bytes'] for r in before),'zip_entries_fully_read_back':len(before),
  'categories':categories,'builder_sha256':sha(builder),'originals_preserved':True,'input_code_executed':False,'native_run':False}
 rr=write_new('checkpoint-receipt.json',encoded(receipt))
 sums=[{'path':'build_checkpoint.py','sha256':sha(builder)},archive_row,*indices,mr,rr]
 write_new('SHA256SUMS',''.join(f"{r['sha256']}  {r['path']}\n" for r in sums).encode())
 print(json.dumps({'archive':archive_row,'manifest_sha256':mr['sha256'],'receipt_sha256':rr['sha256'],'categories':categories,'source_unchanged':True,'native_or_acceptance_claim':False},indent=2))

if __name__=='__main__':main()
