from pathlib import Path
import subprocess,json,hashlib,re,shutil,datetime
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');X=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange');I=Path('/private/tmp/ab34-audit-intake-v2h60oly');H=lambda b:hashlib.sha256(b).hexdigest()
def git(repo,*args):return subprocess.check_output(['git','--no-optional-locks','-C',str(repo),*args])
def tree(repo,rev):
 raw=git(repo,'ls-tree','-r','-z',rev);out={}
 for row in raw.split(b'\0'):
  if not row:continue
  spec,p=row.split(b'\t',1);mode,kind,oid=spec.split();
  if kind==b'blob':out[p.decode()]=oid.decode()
 return out
def blobs(repo,ids):
 unique=list(dict.fromkeys(ids));raw=subprocess.check_output(['git','--no-optional-locks','-C',str(repo),'cat-file','--batch'],input=('\n'.join(unique)+'\n').encode());out={};at=0
 for oid in unique:
  end=raw.index(b'\n',at);parts=raw[at:end].split();assert parts[0].decode()==oid and parts[1]==b'blob';n=int(parts[2]);at=end+1;out[oid]=raw[at:at+n];at+=n;assert raw[at:at+1]==b'\n';at+=1
 assert at==len(raw);return out
intake=json.loads((I/'INTAKE.json').read_text());original=[]
for n in [123,124]:
 r=next(x for x in intake['files'] if x['gate']==n);b=(I/r['intake']).read_bytes();assert len(b)==r['bytes'] and H(b)==r['sha256'] and b==Path(r['source']).read_bytes();d=O/'reports'/r['intake'];d.parent.mkdir(exist_ok=True);d.write_bytes(b);original.append(r|{'copy_sha256':H(b),'original_delivery_has_no_invented_Git_binding':True})
(O/'reports/INTAKE.json').write_bytes((I/'INTAKE.json').read_bytes());(O/'REPORT-DELIVERY-BINDING.json').write_text(json.dumps(original,indent=2)+'\n');allreceipts=[]
for n,slug in [(123,'ch7-run'),(124,'safe-run')]:
 P=R/f'campaign/gates/{n}-{slug}';pub=json.loads((P/'publication.json').read_text());head=git(R,'rev-parse',pub['source']+'^{commit}').decode().strip();rec=git(R,'rev-parse',pub['records']+'^{commit}').decode().strip();ex=git(X,'rev-parse',pub['exchange']+'^{commit}').decode().strip();assert (head,rec,ex)==(pub['source'],pub['records'],pub['exchange']);gdir=f'campaign/gates/{n}-{slug}';srcmap=tree(R,head);recmap=tree(R,rec);xmap=tree(X,ex);paths=git(R,'show',rec+':'+gdir+'/BUNDLE-FILES.txt').decode().splitlines();assert len(paths)==len(set(paths))==pub['sections'];ids=[(srcmap if p.startswith('TCSlib/') else recmap)[p] for p in paths];data=blobs(R,ids);expected=[];sections=[]
 for p,oid in zip(paths,ids):
  b=data[oid];q=b if b.endswith(b'\n') else b+b'\n';q=b'```\n'+q+b'```\n' if p.endswith(('.lean','.py')) else q;expected.append(('## ===== '+p+' =====\n\n').encode()+q);sections.append({'path':p,'Git_revision':head if p.startswith('TCSlib/') else rec,'Git_blob':oid,'bytes':len(b),'sha256':H(b),'bundle_EOF_normalization_added_one_LF':not b.endswith(b'\n')})
 expected=b'\n'.join(expected);bp=pub['folder']+f'/{n}-{slug}-bundle.md';actual=git(X,'show',ex+':'+bp);assert actual==expected and len(actual)==pub['bytes'] and H(actual)==pub['sha256'];checksum_path=pub['folder']+'/SHA256SUMS';checks=git(X,'show',ex+':'+checksum_path).decode().splitlines();checkrows=[]
 for line in checks:
  digest,name=line.split(None,1);name=name.strip().lstrip('*');path=pub['folder']+'/'+name;b=git(X,'show',ex+':'+path);assert H(b)==digest;checkrows.append({'path':path,'sha256':digest,'bytes':len(b)})
 assert len(checkrows)==2
 manifest_counts={}
 for name in ['MANIFEST.json','PAYLOAD-INDEX.json']:
  key=gdir+'/review/'+name;m=json.loads(data[recmap[key]]);rows=m['files'];verified=[]
  for row in rows:
   p=gdir+'/review/'+row['path'];assert p in paths,p;b=data[recmap[p]];assert H(b)==row['sha256'] and len(b)==row['bytes'];verified.append(row)
  manifest_counts[name]=len(verified)
  d=O/str(n)/name;d.parent.mkdir(exist_ok=True);d.write_bytes(data[recmap[key]])
 d=O/str(n);d.mkdir(exist_ok=True)
 for name in ['publication.json','prompt.md','pack.md','BUNDLE-FILES.txt']:(d/name).write_bytes((P/name).read_bytes())
 assert H((P/'prompt.md').read_bytes())==pub['prompt_sha256']
 (d/'SECTION-BINDINGS.json').write_text(json.dumps(sections,indent=2)+'\n');receipt={'gate':n,'source':head,'records':rec,'exchange':ex,'bundle_path':bp,'bundle_sha256':H(actual),'bundle_bytes':len(actual),'sections':len(paths),'all_unique_in_exact_issued_order':True,'all_sections_byte_exact_to_mixed_source_records_Git_blobs':True,'both_checksum_entries':checkrows,'manifest_counts':manifest_counts,'current_prompt_sha256_exact':True,'external_dispatch_confirmed_in_current_publication':pub['external_dispatch_confirmed'],'no_Lean_screen_Git_or_canonical_mutation':True};(d/'BUNDLE-VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n');allreceipts.append(receipt);print(json.dumps(receipt),flush=True)
current=git(R,'rev-parse','HEAD').decode().strip();base='9b5dcf46408db681bcbc721930ef2203fa6bc47d';assert not git(R,'diff','--name-only',base,current,'--','*.lean');(O/'CURRENT-RECORDS-LEAN-BINDING.json').write_text(json.dumps({'records_observed':current,'campaign_Lean_MAC8_base':base,'all_tracked_Lean_blobs_equal_MAC8':True,'this_is_source_Git_check_not_physical_snapshot_or_merge_clearance':True},indent=2)+'\n')
