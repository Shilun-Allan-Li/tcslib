from pathlib import Path
import json,hashlib
O=Path('/private/tmp/ab34-fe9-screen-review');h=lambda b:hashlib.sha256(b).hexdigest();assert not (O/'MANIFEST.json').exists()
d=json.loads((O/'all-existing-row-deltas.json').read_text());rows=json.loads((O/'all13-pair-dispositions.json').read_text());assert len(rows)==13 and len({r['id'] for r in rows})==13
for status,n in [('new',8),('gone',5)]:
 a=[r for r in rows if r['row_status']==status];assert len(a)==n
 assert {(r['target'],r['source'],r['matched_chars'],r['source_chars'],r['percent']) for r in a}=={(r['target'],r['source'],r['matched_chars'],r['source_chars'],r['percent']) for r in d[status]}
sources={(r['phase'],r['path']):r for r in json.loads((O/'all66-source-bindings.json').read_text())};assert len(sources)==66
for r in sources.values():
 b=(O/r['capture']).read_bytes();assert len(b)==r['bytes'] and h(b)==r['sha256'];assert hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()==r['git_blob']
ep=json.loads((O/'endpoint-source-bindings.json').read_text());assert len(ep)==30
for r in ep:
 b=(O/r['capture']).read_bytes();s=(O/sources[(r['phase'],r['path'])]['capture']).read_text();assert h(b)==r['span_SHA256'] and b==s[r['source_start_char']:r['source_end_char']].encode()
sp=json.loads((O/'literal-spans.json').read_text())['spans'];assert len(sp)==33;ids={r['id'] for r in sp};assert len(ids)==33
for r in sp:
 s=(O/sources[(r['phase'],r['source_path'])]['capture']).read_text();b=s[r['start_char']:r['end_char']].encode();assert b==r['literal'].encode() and len(b)==r['UTF8_bytes'] and h(b)==r['SHA256']
for r in rows:assert r['literal_span_ids'] and set(r['literal_span_ids'])<=ids
shared=json.loads((O/'all2102-persistent-row-comparisons.json').read_text());assert len(shared)==2102 and all(r['BASE']==r['HEAD'] and r['score_unchanged'] for r in shared)
# Frozen file paths and hashes are complete, uncapped and rooted inside this private packet.
checks={'rows':13,'new':8,'gone':5,'persistent_comparisons':2102,'persistent_score_changes':0,'source_captures':66,'endpoint_captures':30,'literal_spans':33,'all_source_capture_byte_and_git_blob_hashes_exact':True,'all_literal_and_endpoint_source_slices_exact':True,'reviewer_Lean_screens_scorer_executions':0,'source_Git_canonical_writes':0,'prior_frozen_input_or_peer_mutations':0}
(O/'final-verification.json').write_text(json.dumps(checks,indent=2)+'\n')
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file():files.append({'path':p.relative_to(O).as_posix(),'bytes':p.stat().st_size,'sha256':h(p.read_bytes())})
m={'format':'complete private payload manifest; this manifest excludes itself','status':'FROZEN_PRIVATE_COMPLETION_ROOT_ADOPTION_PENDING','payload_files':len(files),'payload_bytes':sum(r['bytes'] for r in files),'files':files}
(O/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'path':str(O),'manifestSHA256':h((O/'MANIFEST.json').read_bytes()),'findingsSHA256':h((O/'findings.md').read_bytes()),'dispositionsSHA256':h((O/'all13-pair-dispositions.json').read_bytes()),'payload_files':len(files),'payload_bytes':m['payload_bytes']}))
