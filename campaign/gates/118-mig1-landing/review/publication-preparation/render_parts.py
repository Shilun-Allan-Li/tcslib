from pathlib import Path
import json,hashlib,math,datetime
P=Path('/private/tmp/gate118-publication-preparation');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');REL='campaign/gates/118-mig1-landing/review/publication-preparation';PREVIEW=Path('/private/tmp/gate118-publication-preview');PREVIEW.mkdir(exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def loadl(n):return[json.loads(l)for l in(P/n).read_text().splitlines()]
phys=loadl('physical-payloads.jsonl');meta=['pack.candidate.md','TRANSPORT.md','transport-preparation.json','static-preparation-context.json','static-to-candidate-delta.json','ORIGINAL324-LOGICAL.txt','LOGICAL-INPUTS.txt','logical-to-physical.jsonl','physical-payloads.jsonl','BUNDLE-FILES.txt','aliases.json','exact-dedup-map.jsonl','source-bindings.json','frozen-current-input-verification.json','current-replay-binding.json','declared-folder-coverage.json','prepare_transport.py','render_parts.py','validate_candidate.py','bind_current_replay.py','first-collection-checkpoint.json','first-collection-chronology-delta.json','attempts/collector-python-syntax/prepare_transport.py.txt','attempts/collector-python-syntax/failure-note.md','attempts/chronology-HANDOFF-drift/HANDOFF-before.txt','attempts/chronology-HANDOFF-drift/HANDOFF-after.txt','attempts/chronology-HANDOFF-drift/render-preview.json','attempts/chronology-HANDOFF-drift/failure-note.md']
for n in meta:
 q=P/n;assert q.is_file(),n;b=q.read_bytes();b.decode('utf8');phys.insert(meta.index(n),{'path':REL+'/'+n,'bytes':len(b),'sha256':sha(b),'primary_logical':None,'mode':'transport metadata','content_source':str(q),'force_plaintext':True})
assert len({r['path']for r in phys})==len(phys)
def source(r):
 if r['path'].startswith(REL+'/encodings/'):q=P/'encodings'/Path(r['path']).name
 else:q=Path(r['content_source'])
 b=q.read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256']),r['path'];b.decode('utf8');return b
def segment(r):
 b=source(r);pre=('## ===== '+r['path']+' =====\n\n').encode();fence=b'```\n'if r['path'].endswith(('.lean','.py'))else b'';suffix=(b''if b.endswith(b'\n')else b'\n')+fence;return pre+fence+b+suffix,len(pre)+len(fence)
rows=[]
for i,r in enumerate(phys):
 b,_=segment(r);rows.append(r|{'ordinal':i+1,'segment_bytes':len(b),'segment_sha256':sha(b)})
cap=86_000_000;bins=[[],[]];sizes=[0,0];mandatory=set(REL+'/'+n for n in meta)
for r in rows:
 if r['path']in mandatory:bins[0].append(r);sizes[0]+=r['segment_bytes']+1
for r in sorted((r for r in rows if r['path']not in mandatory),key=lambda r:-r['segment_bytes']):
 possible=[i for i in range(len(bins))if sizes[i]+r['segment_bytes']+1<cap]
 if not possible:bins.append([]);sizes.append(0);possible=[len(bins)-1]
 i=min(possible,key=lambda i:sizes[i]);bins[i].append(r);sizes[i]+=r['segment_bytes']+1
parts=[]
for index,rs in enumerate(bins,1):
 rs.sort(key=lambda r:r['ordinal']);name=f'part{index}.md';path=PREVIEW/name;offset=0;segments=[];hasher=hashlib.sha256()
 with path.open('wb')as f:
  for j,r in enumerate(rs):
   if j:f.write(b'\n');hasher.update(b'\n');offset+=1
   b,pre=segment(r);f.write(b);hasher.update(b);segments.append({'path':r['path'],'segment_start':offset,'segment_bytes':len(b),'payload_start':offset+pre,'payload_bytes':r['bytes'],'payload_sha256':r['sha256'],'segment_sha256':sha(b)});offset+=len(b)
 assert offset<90_000_000
 (P/f'BUNDLE-FILES-part{index}.txt').write_text('\n'.join(r['path']for r in rs)+'\n');parts.append({'part':index,'private_preview_path':str(path),'sections':len(rs),'bytes':offset,'sha256':hasher.hexdigest(),'segments':segments})
(P/'combined-physical-payloads.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'),ensure_ascii=False)+'\n'for r in rows));(P/'render-preview.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'records':'candidate,notissued','source':json.loads((P/'transport-preparation.json').read_text())['source'],'combined_physical_sections':len(rows),'parts':parts,'all_parts_under90million_bytes':True,'candidate_metadata_excluded_from_own_part_hash_cycle':['render-preview.json','candidate-validation.json','MANIFEST.json','SHA256SUMS.txt','freeze_preparation.py','partlists/combined rendered index created after rendering'],'preview_MD_files_private_not_committed':True},separators=(',',':'))+'\n');print(json.dumps({'sections':len(rows),'parts':[{k:r[k]for k in ['part','sections','bytes','sha256']}for r in parts]},indent=2))
