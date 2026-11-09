from pathlib import Path
import subprocess,json,hashlib,datetime
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');X=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange');I=Path('/private/tmp/ab34-audit-intake-122-ijodfitp');G='campaign/gates/122-first-halt-reuse';P=R/G;H=lambda b:hashlib.sha256(b).hexdigest()
def git(repo,*args):return subprocess.check_output(['git','--no-optional-locks','-C',str(repo),*args])
def tree(repo,rev):
 out={}
 for row in git(repo,'ls-tree','-r','-z',rev).split(b'\0'):
  if not row:continue
  spec,p=row.split(b'\t',1);mode,kind,oid=spec.split()
  if kind==b'blob':out[p.decode()]=oid.decode()
 return out
def blobs(repo,ids):
 unique=list(dict.fromkeys(ids));raw=subprocess.check_output(['git','--no-optional-locks','-C',str(repo),'cat-file','--batch'],input=('\n'.join(unique)+'\n').encode());out={};at=0
 for oid in unique:
  end=raw.index(b'\n',at);parts=raw[at:end].split();assert parts[0].decode()==oid and parts[1]==b'blob';n=int(parts[2]);at=end+1;out[oid]=raw[at:at+n];at+=n;assert raw[at:at+1]==b'\n';at+=1
 assert at==len(raw);return out
pub=json.loads((P/'publication.json').read_text());src=pub['source'];rec=pub['records'];ex=pub['exchange']
for repo,rev in [(R,src),(R,rec),(X,ex)]:assert git(repo,'rev-parse',rev+'^{commit}').decode().strip()==rev
sm=tree(R,src);rm=tree(R,rec);paths=git(R,'show',rec+':'+G+'/BUNDLE-FILES.txt').decode().splitlines();assert len(paths)==len(set(paths))==1527
pm=json.loads(git(R,'show',rec+':'+G+'/PATH-MAP.json'));mp=pm['paths'];assert len(mp)==2437
ids=[(sm if p.startswith('TCSlib/') else rm)[p] for p in paths]+[rm[p] for p in mp.values()];data=blobs(R,ids);sec=[];bs=[]
for p in paths:
 oid=(sm if p.startswith('TCSlib/') else rm)[p];b=data[oid];q=b if b.endswith(b'\n') else b+b'\n';q=b'```\n'+q+b'```\n' if p.endswith(('.lean','.py')) else q;bs.append(('## ===== '+p+' =====\n\n').encode()+q);sec.append({'path':p,'Git_revision':src if p.startswith('TCSlib/') else rec,'Git_blob':oid,'bytes':len(b),'sha256':H(b),'appended_one_LF':not b.endswith(b'\n')})
expected=b'\n'.join(bs);actual=git(X,'show',ex+':'+pub['folder']+'/122-first-halt-reuse-bundle.md');assert actual==expected and len(actual)==pub['bytes'] and H(actual)==pub['sha256']
checks=[]
for line in git(X,'show',ex+':'+pub['folder']+'/SHA256SUMS').decode().splitlines():
 digest,name=line.split(None,1);name=name.strip().lstrip('*');b=git(X,'show',ex+':'+pub['folder']+'/'+name);assert H(b)==digest;checks.append({'name':name,'sha256':digest,'bytes':len(b)})
assert len(checks)==2
get=lambda rel:data[rm[mp[rel]]]
m=json.loads(get('MANIFEST.json'));assert H(get('MANIFEST.json'))==pm['source_manifest_sha256'];assert len(m['files'])==2437
verified=[]
for row in m['files']:
 b=get(row['path']);assert len(b)==row['bytes'] and H(b)==row['sha256'];verified.append(row)
u=json.loads(get('BUNDLE-UNIVERSE.json'));om=json.loads(get('BUNDLE-OMISSION-RECOVERY.json'));ret=get('BUNDLE-FILES.portable.txt').decode().splitlines();assert len(ret)==len(set(ret))==1423;assert len(om['omissions'])==1016
assert set(ret)<=set(mp);assert len(set(ret)|{x['omitted_path'] for x in om['omissions']})==2439 # root manifest and checksum supplement payload manifest
for row in om['omissions']:
 a=row['omitted_path'];b=row['recover_from_retained_path'];assert a not in ret and b in ret and row['one_hop'];assert get(a)==get(b);assert H(get(a))==row['sha256'] and len(get(a))==row['bytes'];assert mp[a] not in paths and mp[b] in paths
for row in u['files']:
 b=get(row['path']);assert len(b)==row['bytes'] and H(b)==row['sha256']
assert len(u['files'])==2430
for p in ret:assert mp[p] in paths,p
intake=json.loads((I/'INTAKE.json').read_text());report=(I/'gate122-first-halt-reuse-findings.md').read_bytes();assert len(report)==intake['bytes']==5785 and H(report)==intake['sha256'];assert Path(intake['original_path']).read_bytes()==report==(P/'findings.md').read_bytes()
(O/'report-original.md').write_bytes(report);(O/'INTAKE.json').write_bytes((I/'INTAKE.json').read_bytes());(O/'DELIVERY.json').write_text(json.dumps(intake|{'current_canonical_findings_byte_exact':True,'local_delivery_has_no_invented_Git_binding':True},indent=2)+'\n')
for name in ['publication.json','prompt.md','pack.md','PATH-MAP.json']:(O/name).write_bytes((P/name).read_bytes())
assert H((P/'prompt.md').read_bytes())==pub['prompt_sha256']
(O/'SECTION-BINDINGS.json').write_text(json.dumps(sec,indent=2)+'\n');(O/'LOGICAL-PAYLOAD-BINDINGS.json').write_text(json.dumps([r|{'canonical':mp[r['path']],'Git_blob':rm[mp[r['path']]],'included_directly_in_issued_bundle':mp[r['path']] in paths} for r in verified],indent=2)+'\n')
cur=git(R,'rev-parse','HEAD').decode().strip();base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';assert not git(R,'diff','--name-only',base,cur,'--','*.lean')
receipt={'observed_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':src,'records':rec,'exchange':ex,'bundle_sha256':H(actual),'bytes':len(actual),'ordered_sections':len(paths),'checksum_entries':checks,'all_section_bytes_rebuilt_exact':True,'logical_payload_manifest_entries':len(verified),'all_physical_record_payload_Git_blobs_verified':True,'core_inventory':len(u['files']),'portable_retained':len(ret),'one_hop_exact_aliases':len(om['omissions']),'complete_alias_recovery_verified_by_byte_equality':True,'current_records':cur,'current_campaign_Lean_exact_MAC8':True,'new_execution':'byte/hash/Git-read checks only; no Lean, screen, lint, static helper or extraction execution','physical_snapshot_not_checked':True}
(O/'BINDING-VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
