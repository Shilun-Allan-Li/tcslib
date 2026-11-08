from pathlib import Path
import json,io,tarfile,gzip,base64,hashlib
B=Path(__file__).resolve().parents[1];cfg=json.loads((B/'qa/config.json').read_text());A=B/'qa/encoded-exports';A.mkdir();archiveRows=[]
for phase in ['BASE','HEAD']:
 root=Path(cfg[phase+'_export']);entries=[];buff=io.BytesIO()
 with tarfile.open(fileobj=buff,mode='w',format=tarfile.PAX_FORMAT)as tar:
  for p in sorted(root.rglob('*')):
   assert not p.is_symlink(),p
   if not p.is_file():continue
   rel=p.relative_to(root).as_posix();assert not rel.startswith('/')and'..'not in Path(rel).parts
   data=p.read_bytes();data.decode('utf-8');info=tarfile.TarInfo(rel);info.size=len(data);info.mode=0o644;info.uid=info.gid=0;info.mtime=0;tar.addfile(info,io.BytesIO(data));entries.append({'path':rel,'bytes':len(data),'SHA256':hashlib.sha256(data).hexdigest()})
 compressed=gzip.compress(buff.getvalue(),compresslevel=9,mtime=0);text=base64.encodebytes(compressed);f=A/(phase+'-QA-export.tar.gz.base64.txt');f.write_bytes(text)
 # Full lossless self-verification; no extraction outside private memory.
 decoded=base64.decodebytes(text);assert decoded==compressed
 with tarfile.open(fileobj=io.BytesIO(gzip.decompress(decoded)),mode='r:')as tar:
  members=tar.getmembers();assert len(members)==len(entries)
  for member,row in zip(members,entries):assert member.isfile()and member.name==row['path']and hashlib.sha256(tar.extractfile(member).read()).hexdigest()==row['SHA256']
 archiveRows.append({'phase':phase,'encoded_file':str(f.relative_to(B)),'encoded_SHA256':hashlib.sha256(text).hexdigest(),'gzip_SHA256':hashlib.sha256(compressed).hexdigest(),'tar_SHA256':hashlib.sha256(buff.getvalue()).hexdigest(),'members':entries,'member_count':len(entries),'all_members_regular_UTF8':True,'lossless_decode_verified':True})
(A/'ARCHIVE-MEMBERS.json').write_text(json.dumps({'scope':'Complete working QA exports supplied losslessly; raw33-per-phase captures are also directly bundled. No compiled objects, private PDFs or symlinks.','archives':archiveRows},indent=2)+'\n')
# Explicit per-file roles keep historical and failed evidence out of current claims.
roles=[]
F=B/'evidence/nine-boundary';primary=['attempts/'+x+'/'for x in ['05-EXP-full-boundary','06-XR-full-boundary','10-InputCall-field-reader-native','11-InputCall-field-reader-sealed','12-Hardness-retained5-prefix-sealed','13-retained9-controls-base','14-retained9-controls-sealed']]
for p in sorted(F.rglob('*')):
 if not p.is_file():continue
 rel=str(p.relative_to(F))
 if any(rel.startswith(x)for x in primary):role='Successful current-nine scope receipt, transported by exact CODE-LINEAGE; original execution pin retained'
 elif rel.startswith('bindings/prior-'):role='HISTORICAL a93/11-root binding only; NOT current validation'
 elif rel.startswith('attempts/'):role='Diagnostic, failed, held-target or preparatory auxiliary receipt; NOT counted as current-nine passing execution unless listed in primary set'
 else:role='Full source/helper/index/context supporting the bounded nine-root checks; no independent PASS inferred'
 roles.append({'path':str(p.relative_to(B)),'role':role})
F=B/'evidence/compact-census'
for p in sorted(F.rglob('*')):
 if not p.is_file():continue
 rel=str(p.relative_to(F));role='Current fresh d64 four-owner bounded ABI50/full AX/default-simp evidence'
 if rel.startswith('attempts/01-BASE/'):role='INVALID initial fixture; retained and excluded from successful census'
 roles.append({'path':str(p.relative_to(B)),'role':role})
F=B/'evidence/replay-NFE2'
for p in sorted(F.rglob('*')):
 if p.is_file():roles.append({'path':str(p.relative_to(B)),'role':'Actual current d64 prospective-tree 157-module replay data; no snapshot object bundled'})
(B/'bindings/EVIDENCE-ROLES.json').write_text(json.dumps({'no_old11_census_or_native_pass_used_as_current':True,'no_256MB_old_census_included':True,'rows':roles},indent=2)+'\n')
print(json.dumps({'encoded_exports':[{'phase':r['phase'],'members':r['member_count'],'gzip_bytes':len(base64.decodebytes((B/r['encoded_file']).read_bytes()))}for r in archiveRows],'uncapped_evidence_role_rows':len(roles)}))
