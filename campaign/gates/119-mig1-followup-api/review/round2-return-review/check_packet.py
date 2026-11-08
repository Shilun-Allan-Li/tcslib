from pathlib import Path
import subprocess,hashlib,json,re,datetime
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
O=Path('/private/tmp/gate119-round2-return-review')
GP='campaign/gates/119-mig1-followup-api'
S='f1ca767a10551960faf36ad9c8ff17bea3a2d88c'; B='3023dc1408c3d216fc07a7cbba9ae30135b861ed'; C='bf02e7ccd9d0b76d38d4da8d03d31984945fe5b4'; X='1e308d23c6646d9db5b7ee8420f3e9500c467544'
XP='arora-barak-ch3-4/outbox/gates/119-mig1-followup-api-r2-gate'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def blob(pin,path):return git('show',pin+':'+path)
def framed(section,raw,path):
 if section.startswith(raw) and section[len(raw):] in [b'',b'\n',b'\n\n']:
  return repr(section[len(raw):])
 f=re.match(rb'(`{3,})\n',section);assert f,(path,'framing prefix')
 body=section[f.end():];assert body.startswith(raw),(path,'payload')
 tail=body[len(raw):];assert tail in [f[1]+b'\n',f[1]+b'\n\n',b'\n'+f[1]+b'\n',b'\n'+f[1]+b'\n\n'],(path,'framing suffix',repr(tail))
 return repr(section[:f.end()])+':'+repr(tail)
def objects(items):
 p=subprocess.run(['git','-C',str(R),'cat-file','--batch'],input=b''.join((i['pin']+':'+i['path']+'\n').encode() for i in items),stdout=subprocess.PIPE,check=True)
 b=p.stdout; q=0; out=[]
 for i in items:
  n=b.index(b'\n',q); h=b[q:n].decode().split(); assert h[1]=='blob',h
  sz=int(h[2]); st=n+1; raw=b[st:st+sz]; assert b[st+sz:st+sz+1]==b'\n'; q=st+sz+1
  out.append((h[0],raw))
 assert q==len(b)
 return out
pins={}
for p in [S,B,C,X,'8d58d0cf63be3fdd24bbb929d859562972c17931','c40d52d570953d32b570bf4c9eeecc07e24e23f1','1160c18f03fd318f0dec25738790935fa61379d4','626b1a81ddd33f4b0e0dabd4e874a16a0fe71724']:
 v=git('rev-parse',p+'^{commit}').decode().strip();git('cat-file','-e',v+'^{commit}');pins[p]=v
rep=(R/GP/'findings-r2.md').read_bytes(); assert len(rep)==16007 and sha(rep)=='347c5dce214326bc41defed4f5b69a05a67883add872e69fa52a761da24a562d'
rows=re.findall(rb'^\| ([0-9]+) \| ([a-z]+) \|',rep,re.M); assert [(int(n),s.decode()) for n,s in rows]==[(i,'note') for i in range(1,18)]
assert rep.decode().splitlines()[-1]=='Verdict: PASS — blocker 0 / major 0 / minor 0 / note 17.'
rc=json.loads((R/GP/'findings-r2-receipt.json').read_bytes());assert rc['bytes']==len(rep) and rc['sha256']==sha(rep)
result={'review_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'Independently authored stdlib validators; Git read-only; no supplied programs executed','pins_verified':pins,'report':{'bytes':len(rep),'sha256':sha(rep),'notes':17,'verdict':'PASS 0/0/0/17'}}
def check_bundle(x,xp,expected_sha,expected_bytes,n,idx_path=None):
 bundle=blob(x,xp+'/'+xp.split('/')[-1].replace('-gate','-bundle.md'))
 assert len(bundle)==expected_bytes and sha(bundle)==expected_sha
 bundle.decode('utf8')
 order=blob(x,xp+'/BUNDLE-FILES.txt').decode().splitlines();assert len(order)==n and len(set(order))==n
 index=json.loads(blob(x,xp+'/INPUT-INDEX.json')) if idx_path is None else json.loads(idx_path.read_bytes())
 assert index['sections']==n and [i['path'] for i in index['items']]==order
 matches=list(re.finditer(rb'^## ===== ([^\n]+) =====\n\n',bundle,re.M));assert len(matches)==n
 assert [m.group(1).decode() for m in matches]==order and matches[0].start()==0
 items=[];suffixes={};alljson=0;empty=[]
 for j,((oid,raw),i,m) in enumerate(zip(objects(index['items']),index['items'],matches)):
  raw.decode('utf8'); assert len(raw)==i['bytes'] and sha(raw)==i['sha256']
  assert i['pin']==(S if i['path'].startswith('TCSlib/') and i['path'].endswith('.lean') else index['records']),i
  nxt=matches[j+1].start() if j+1<n else len(bundle)
  section=bundle[m.end():nxt];suffix=framed(section,raw,i['path'])
  suffixes[suffix]=suffixes.get(suffix,0)+1
  if not raw:empty.append(i['path'])
  if i['path'].endswith('.json'):json.loads(raw);alljson+=1
  items.append({**i,'git_blob':oid,'payload_exact':True,'transport_suffix':suffix})
 assert sum(i['bytes'] for i in items)==index['raw_payload_bytes']
 sums=blob(x,xp+'/SHA256SUMS').decode().splitlines()
 for ln in sums:
  h,f=ln.split(None,1); f=f.lstrip('* ');assert sha(blob(x,xp+'/'+f))==h,(f,h)
 return {'exchange':x,'bundle_sha256':sha(bundle),'bundle_bytes':len(bundle),'sections':n,'JSONs':alljson,'empty':empty,'transport_suffixes':suffixes,'README_checksums_exact':True,'items':items},index
new,idx=check_bundle(X,XP,'1f14e6f2a9bba9e6fe7b575bb9a546d6a89c7457c79b30d677ffb0ff19da36b3',79315563,703)
# The original packet has no machine index; recover every payload from its ordered pinned blobs.
OX='8d58d0cf63be3fdd24bbb929d859562972c17931'; OC='c40d52d570953d32b570bf4c9eeecc07e24e23f1'; OXP='arora-barak-ch3-4/outbox/gates/119-mig1-followup-api-gate'
ob=blob(OX,OXP+'/119-mig1-followup-api-bundle.md');assert len(ob)==76546940 and sha(ob)=='60a0b7ca5095ee1c619c4343aa59f1010054bcefaa39daec08bb91de89ef8a0e'
order=blob(OX,OXP+'/BUNDLE-FILES.txt').decode().splitlines();assert len(order)==640
m=list(re.finditer(rb'^## ===== ([^\n]+) =====\n\n',ob,re.M));assert [z.group(1).decode() for z in m]==order
old_items=[{'path':p,'pin':S if p.startswith('TCSlib/') and p.endswith('.lean') else OC} for p in order]; olds={};oldchecks=[]
for j,(i,(oid,raw)) in enumerate(zip(old_items,objects(old_items))):
 nxt=m[j+1].start() if j+1<len(m) else len(ob);sec=ob[m[j].end():nxt]
 framed(sec,raw,i['path'])
 oldchecks.append({**i,'bytes':len(raw),'sha256':sha(raw),'git_blob':oid});olds[i['path']]=raw
newmap={i['path']:i for i in new['items']};unchanged=[];updated=[]
for p,v in olds.items():
 assert p in newmap,p
 (unchanged if sha(v)==newmap[p]['sha256'] else updated).append(p)
assert len(unchanged)==635 and len(updated)==5
part=json.loads(blob(C,GP+'/review/round2-pack/round1-to-round2-input-partition.json'))
result['partition_data']=part
result['old_bundle']={'bytes':len(ob),'sha256':sha(ob),'sections':640,'payloads_exact':640,'unchanged_in_round2':635,'updated_records':updated}
result['round2_bundle']={k:v for k,v in new.items() if k!='items'}
# Verify every complete old capture, using the explicit original/capture fields after schema inspection.
result['round2_index_SHA256']=sha(blob(X,XP+'/INPUT-INDEX.json'))
result['current_records_head_observed']=git('rev-parse','HEAD').decode().strip()
(O/'packet-check.json').write_text(json.dumps(result,indent=2)+'\n')
(O/'packet-sections.json').write_text(json.dumps(new['items'],indent=2)+'\n')
(O/'original-packet-sections.json').write_text(json.dumps(oldchecks,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='partition_data'},indent=2))
print('PARTITION SCHEMA',str(part)[:1800])
