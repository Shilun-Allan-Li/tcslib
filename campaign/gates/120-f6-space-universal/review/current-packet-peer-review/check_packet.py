from pathlib import Path
import json,hashlib,subprocess,base64,gzip,re,io,datetime,collections
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');GP='campaign/gates/120-f6-space-universal';FP=GP+'/review/final-publication-preparation';F=R/FP;O=Path('/private/tmp/f6-gate120-peer-review');S='0d0950caeb39300b5cc9bf41e5f07392fb26d3e5';B='3023dc1408c3d216fc07a7cbba9ae30135b861ed';OC='f41bdaea207724606d8934bfc2c9a823c5dd1e2f';X='2adb80788611696d2cad6f907285c0c5a197ae09'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def blob(pin,p):return git('show',pin+':'+p)
def j(p):return json.loads(p.read_bytes())
mr=(F/'MANIFEST.json').read_bytes();assert sha(mr)=='0a30be687afea1f19d5ccffa2f0a85d0d1574d6380b718da789124771436c66c';m=json.loads(mr)
for row in m['files']:
 b=(F/row['path']).read_bytes();assert (len(b),sha(b))==(row['bytes'],row['sha256'])
assert len([p for p in F.rglob('*') if p.is_file()])==45
paths=(F/'BUNDLE-FILES-final-draft.txt').read_text().splitlines();assert len(paths)==len(set(paths))==1413
inv=j(F/'input-inventory.json');im={x['path']:x for x in inv['files']};assert len(im)==1368
own={FP+'/'+x['path']:x for x in m['files']};own[FP+'/MANIFEST.json']={'bytes':len(mr),'sha256':sha(mr)};assert len(own)==45 and not im.keys()&own.keys();assert set(paths)==im.keys()|own.keys()
pack=(F/'canonical-pack-draft.md').read_bytes();assert sha(pack)=='528f9c8e0373e5c56d9422efc65f3ee9b52e2f96423010aa4966c90970c12051'
override=inv['prospective_canonical_override'];assert override['path']==GP+'/pack.md' and override['draft']==FP+'/canonical-pack-draft.md'
# Read every prospective payload by the actual mixed-pin rule. Every committed source is a Git blob.
problems=[];payloads={};items=[];total=0;jsons=0;post_freeze_records_drift=[]
for p in paths:
 row=im.get(p,own.get(p))
 raw=blob(S,p) if p.startswith('TCSlib/') else pack if p==GP+'/pack.md' else (R/p).read_bytes()
 if (len(raw),sha(raw))!=(row['bytes'],row['sha256']):
  historical=blob(inv['observed_records_not_final'],p)
  if (len(historical),sha(historical))==(row['bytes'],row['sha256']):
   post_freeze_records_drift.append({'path':p,'frozen_candidate_pin':inv['observed_records_not_final'],'frozen_bytes':len(historical),'frozen_sha256':sha(historical),'current_bytes':len(raw),'current_sha256':sha(raw),'final_rebind_root_owned':True})
   raw=historical
  else:problems.append({'path':p,'inventory':row,'actual_bytes':len(raw),'actual_sha256':sha(raw)})
 raw.decode('utf8');payloads[p]=raw;total+=len(raw)
 if p.endswith('.json'):json.loads(raw);jsons+=1
 items.append({'path':p,'bytes':len(raw),'sha256':sha(raw),'binding':'source:'+S if p.startswith('TCSlib/') else 'prospective canonical override' if p==GP+'/pack.md' else 'records candidate'})
assert not problems,problems
assert total==65762521
sources=j(F/'source-bindings.json')['all_source_rows'];assert len(sources)==23 and {x['path'] for x in sources}=={p for p in paths if p.startswith('TCSlib/')}
for x in sources:assert blob(S,x['path'])==payloads[x['path']] and git('rev-parse',S+':'+x['path']).decode().strip()==x['git_blob'] and (len(payloads[x['path']]),sha(payloads[x['path']]))==(x['bytes'],x['sha256'])
# Full original624 exact literal path/order prefix and exact immutable original bundle reconstruction.
origorder=blob(OC,'campaign/fills/f6/BUNDLE-FILES.txt').decode().splitlines();assert len(origorder)==624 and paths[:624]==origorder
parts=[];olds={}
for p in origorder:
 raw=blob(B if p.startswith('TCSlib/') else OC,p);olds[p]=raw;content=raw+(b'' if raw.endswith(b'\n') else b'\n')
 if p.endswith(('.lean','.py')):content=b'```\n'+content+b'```\n'
 parts.append(('## ===== '+p+' =====\n\n').encode()+content)
issued=b'\n'.join(parts);assert (len(issued),sha(issued))==(8707327,'8fa482702846898f7fa04c4e1b0aa012300b4febaa6385ee8caa869cf14740be')
assert issued==blob(X,'arora-barak-ch3-4/outbox/fills/f6-space-universal/f6-space-universal-bundle.md')
partition=j(F/'issued-to-current-partition.json');assert [x['path'] for x in partition['all624_files']]==origorder
updated=[]
for x in partition['all624_files']:
 p=x['path'];old=olds[p];now=payloads[p];assert (len(old),sha(old))==(x['issued']['bytes'],x['issued']['sha256']);assert (len(now),sha(now))==(x['current']['bytes'],x['current']['sha256'])
 if old!=now:
  assert 'full_issued_capture' in x and payloads[x['full_issued_capture']]==old;updated.append(p)
assert len(updated)==5
# All large metadata substitutions are exact data, no source/control/raw-score cap.
sub=j(F/'UTF8-substitution-receipt.json');trans=sub['transforms'];assert len(trans)==31 and len({x['representation'] for x in trans})==22;tm={x['original']:x['representation'] for x in trans};assert not set(tm)&set(origorder)
transchecks=[]
for x in trans:
 enc=payloads[x['representation']];gz=base64.b64decode(b''.join(enc.split()),validate=True);raw=gzip.decompress(gz)
 for b,key in [(enc,'encoded'),(gz,'gzip'),(raw,'raw')]:assert (len(b),sha(b))==(x[key]['bytes'],x[key]['sha256'])
 assert raw==(R/x['original']).read_bytes() and not x['source_capture'];raw.decode('utf8')
 if x['original'].endswith('.json'):json.loads(raw)
 transchecks.append({'original':x['original'],'representation':x['representation'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'exact_original_bytes':True})
# Full binary alias bindings, including old10/new8 and optional full gzip data; never execute payloads.
ba=j(F/'binary-alias-receipt.json');aliases=ba['archives'];assert len(aliases)==18
am={x['original']:x['representation'] for x in aliases};aliaschecks=[]
for x in aliases:
 enc=payloads[x['representation']];raw=base64.b64decode(b''.join(enc.split()),validate=True)
 assert (len(enc),sha(enc))==(x['encoded']['bytes'],x['encoded']['sha256']);assert (len(raw),sha(raw))==(x['raw']['bytes'],x['raw']['sha256']);assert raw==(R/x['original']).read_bytes()
 aliaschecks.append({'original':x['original'],'representation':x['representation'],'raw_bytes':len(raw),'raw_sha256':sha(raw),'exact_original_bytes':True})
# Every old815 path and every uncapped current F6 file has a literal or a fully validated alias.
old815=(R/GP/'review/packet-draft/BUNDLE-FILES.candidate.txt').read_text().splitlines();assert len(old815)==815
rep=lambda p:p if p in payloads else tm.get(p,am.get(p))
assert all(rep(p) in payloads for p in old815)
cov=j(F/'folder-coverage.json');folderchecks=[]
for d in cov['folders']:
 names={str(p.relative_to(R)) for p in (R/d['folder']).rglob('*') if p.is_file() and not str(p.relative_to(R)).startswith(FP+'/')}
 rows=d['rows'];declared={x['original'] for x in rows}
 # Existing gate scope is a documented creation-time inventory; no future review folder is silently included.
 assert len(rows)==d['files'] and declared<=names
 if d['folder']=='campaign/fills/f6':assert names==declared
 for x in rows:
  assert x['represented_by']==rep(x['original']) and x['represented_by'] in payloads,(x,rep(x['original']))
 folderchecks.append({'folder':d['folder'],'declared_files':len(rows),'all_represented_exactly':True,'current_extra_paths':sorted(names-declared)})
# Included replay generators have their direct graph dependency and the archived actual copies.
hp=j(F/'helper-provenance.json')
for x in hp['helpers']:
 assert x['path'] in payloads and (len(payloads[x['path']]),sha(payloads[x['path']]))==(x['bytes'],x['sha256'])
assert payloads['devtools/seyoon/graph.py']==payloads[FP+'/graph.py.txt']==payloads['campaign/fills/f6/landing/replay-mf62/graph.py.txt']
# Prospective framing/render digest is computed by own code, not a delivered bundler execution.
bundlehash=hashlib.sha256();rendered=0
for i,p in enumerate(paths):
 raw=payloads[p];content=raw+(b'' if raw.endswith(b'\n') else b'\n')
 if p.endswith(('.lean','.py')):content=b'```\n'+content+b'```\n'
 segment=(b'\n' if i else b'')+('## ===== '+p+' =====\n\n').encode()+content;bundlehash.update(segment);rendered+=len(segment)
# Exact root-planned records-only reorder, with the required Codex paragraph last.
text=pack.decode();a=text.index('## Adversarial/model review and return');q=text.index('## Publication input fidelity');assert q>a
publication=text[q:];front=text[:a];returns=text[a:q];reordered=front+publication+'\n'+returns
assert publication in reordered and returns in reordered and reordered.rstrip().endswith('wrapping), and also paste its content in your reply.')
assert 'CURRENT_SEALS_FINAL_RECEIPTS_PENDING' not in reordered and 'SCREEN23_FINAL_RESULTS_PENDING' not in reordered
(O/'pre-adoption-in-memory-reorder.md').write_text(reordered)
(O/'pre-adoption-in-memory-reorder.patch').write_text(''.join(__import__('difflib').unified_diff(text.splitlines(keepends=True),reordered.splitlines(keepends=True),fromfile='frozen-canonical-draft',tofile='pre-adoption-in-memory-reorder')))
out={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'frozen_preparation_manifest_sha256':sha(mr),'frozen_canonical_pack_sha256':sha(pack),'source':S,'source_binding_count':23,'candidate_sections':len(paths),'all_candidate_payload_bytes':total,'all_candidate_payloads_exact':True,'candidate_JSON_sections_parsed':jsons,'prospective_rendered_bundle_bytes_before_root_reorder':rendered,'prospective_rendered_bundle_sha256_before_root_reorder':bundlehash.hexdigest(),'original624_literal_prefix_and_exact_bundle_rebuilt':True,'issued_changed_inputs_with_full_old_captures':updated,'full815_scope_represented':True,'metadata_substitutions':transchecks,'binary_aliases':aliaschecks,'full_folder_coverage':folderchecks,'graph_and_transitive_helpers_present':True,'known_root_adoption_correction':{'action':'Move Publication input fidelity section before Adversarial/model review and return so Codex delivery paragraph closes pack','whole_text_preserved':True,'proposed_reordered_pack_bytes':len(reordered.encode()),'proposed_reordered_pack_sha256':sha(reordered.encode()),'root_must_rebind_final_records_and_render':True},'post_freeze_records_drift':post_freeze_records_drift,'no_supplied_program_or_payload_executed':True}
(O/'packet-check.json').write_text(json.dumps(out,indent=2)+'\n');(O/'candidate-inputs-verified.json').write_text(json.dumps(items,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['metadata_substitutions','binary_aliases']},indent=2))
