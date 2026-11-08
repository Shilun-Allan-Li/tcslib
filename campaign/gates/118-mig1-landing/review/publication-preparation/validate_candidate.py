from pathlib import Path
import json,hashlib,gzip,base64,collections,datetime
P=Path('/private/tmp/gate118-publication-preparation');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');REL='campaign/gates/118-mig1-landing/review/publication-preparation'
def sha(b):return hashlib.sha256(b).hexdigest()
def rows(n):return[json.loads(l)for l in(P/n).read_text().splitlines()]
logical=rows('logical-to-physical.jsonl');phys=rows('physical-payloads.jsonl');by={r['path']:r for r in phys};assert len(by)==len(phys);cache={}
for p,r in by.items():
 q=P/'encodings'/Path(p).name if p.startswith(REL+'/encodings/')else Path(r['content_source']);b=q.read_bytes();assert(len(b),sha(b))==(r['bytes'],r['sha256']),p;b.decode('utf8');cache[p]=b
aliases=json.loads((P/'aliases.json').read_text());assert set(r['payload']for r in aliases)==set(REL+'/encodings/'+q.name for q in(P/'encodings').iterdir()if q.is_file())
restored={};used=collections.Counter()
for r in logical:
 p=r['physical'];used[p]+=1;key=(p,r['decode'])
 if key not in restored:restored[key]=gzip.decompress(base64.decodebytes(cache[p]))if r['decode']=='gzip+base64'else cache[p]
 b=restored[key];assert(len(b),sha(b))==(r['bytes'],r['sha256']),r['logical'];q=R/(r['source_capture']if r['logical'].startswith('TCSlib/')else r['logical']);assert q.read_bytes()==b,r['logical']
assert set(used)==set(by)and len({r['logical']for r in logical})==len(logical)
expected=(P/'LOGICAL-INPUTS.txt').read_text().splitlines();assert expected==[r['logical']for r in logical];orig=(R/'campaign/fills/mig1/BUNDLE-FILES.txt').read_text().splitlines();assert len(orig)==324 and expected[:324]==orig
coverage=json.loads((P/'declared-folder-coverage.json').read_text());actual={}
for folder,listed in coverage['folders'].items():
 now=sorted(str(q.relative_to(R))for q in(R/folder).rglob('*')if q.is_file());assert now==listed,{'folder':folder,'added':sorted(set(now)-set(listed)),'gone':sorted(set(listed)-set(now))};assert set(now)<=set(expected);actual[folder]=len(now)
pins=json.loads((P/'source-bindings.json').read_text());assert len(pins)==50
for r in pins:
 assert r['capture']in by and by[r['capture']]['mode']=='identity';b=cache[r['capture']];assert(len(b),sha(b))==(r['bytes'],r['sha256']);blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert blob==r['capture_git_binding']['blob']
 if r['side']=='head':assert r['path']in by and by[r['path']]['mode']=='identity'and cache[r['path']]==b
B=R/'campaign/fills/mig1/landing/post234-compiled-accounting/baseline-current/source-captures/Base'
for r in pins:
 if r['side']=='base'and(B/(r['path']+'.txt')).exists():assert cache[r['capture']]==(B/(r['path']+'.txt')).read_bytes()
pack=(P/'pack.candidate.md').read_text();assert pack.rstrip().endswith('**Deliver your findings as a downloadable file named `gate118-mig1-landing-findings.md`** (the findings table and the verdict line, no other wrapping), and also paste its content in your reply.');assert pack.count('CURRENT_MMIG3_STATUS: ACTUAL PASS394/0')==1 and 'CURRENT_MMIG3_STATUS: PENDING.'not in pack
# Independent indexed segment checks avoid confusing embedded old bundle headings with new sections.
preview=json.loads((P/'render-preview.json').read_text());combined=rows('combined-physical-payloads.jsonl');cp={r['path']:r for r in combined};seen=[]
for part in preview['parts']:
 data=Path(part['private_preview_path']).read_bytes();assert(len(data),sha(data))==(part['bytes'],part['sha256'])and len(data)<90_000_000
 order=(P/f"BUNDLE-FILES-part{part['part']}.txt").read_text().splitlines();assert order==[r['path']for r in part['segments']]
 for seg in part['segments']:
  p=seg['path'];r=cp[p];payload=data[seg['payload_start']:seg['payload_start']+seg['payload_bytes']];assert(len(payload),sha(payload))==(r['bytes'],r['sha256']);raw=data[seg['segment_start']:seg['segment_start']+seg['segment_bytes']];assert sha(raw)==seg['segment_sha256'];assert raw.startswith(('## ===== '+p+' =====\n\n').encode());seen.append(p)
assert len(seen)==len(set(seen))==len(cp)==preview['combined_physical_sections']and set(seen)==set(cp)
result={'validated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'logical_inputs':len(logical),'all_original13438_paths_retained':True,'original324_scope_and_order_exact':True,'all_logical_payloads_reconstructed_byte_exact':True,'all_actual_candidate_bytes_rechecked':True,'physical_evidence_payloads':len(by),'all_physical_payloads_used':True,'selected_encoding_payloads':len(aliases),'no_unused_encoding_file':True,'full_folder_coverage':actual,'current_plaintext50plusROOT25_exact':True,'all50_Git_blob_SHA1_reconstructed':True,'no_Git_command_executed':True,'source_pin_authority':'frozen captures/static supplied pin agreement; root final Git mixed index remains required','parts':[{k:r[k]for k in ['part','sections','bytes','sha256']}for r in preview['parts']],'all_rendered_sections_independently_index_verified':True,'all_parts_under90million_bytes':True,'required_Codex_delivery_paragraph_last':True,'MMIG3_complete18_folder_and394PASS_bound':True,'no_dispatch_merge_clearance_or_gate_action':True};(P/'candidate-validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
