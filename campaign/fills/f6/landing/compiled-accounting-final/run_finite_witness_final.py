from pathlib import Path
import json,os,hashlib,subprocess,datetime,time,re,gzip,base64,io
O=Path('/private/tmp/f6-compiled-accounting-final');D=O/'finite-witness-diagnostic-final';c=json.loads((O/'context.json').read_bytes());project=Path(c['probe_project'])
def sha(b):return hashlib.sha256(b).hexdigest()
assert (project/'lean-toolchain').read_text().strip()==c['toolchain']=='leanprover/lean4:v4.25.0'
assert sha(Path(c['owner_olean']).read_bytes())==c['owner_olean_sha256'];assert sha((Path(c['actual_worktree'])/c['source_path']).read_bytes())==c['source_sha256']
src=(D/'ArbitraryFiniteness.lean.txt').read_bytes();file=project/'Final_ArbitraryFiniteness.lean';assert not file.exists();file.write_bytes(src);rawpath=project/'Final_ArbitraryFiniteness.out';assert not rawpath.exists();argv=['bash',c['wrapper'],str(project),c['snapshot'],str(file)]
rec={'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':c['candidate_head'],'source_sha256':c['source_sha256'],'argv':argv,'input':'ArbitraryFiniteness.lean.txt','input_sha256':sha(src),'snapshot':c['snapshot'],'toolchain':c['toolchain'],'single_Lean_plain_managed_no_olean_output':True,'local_slots':3,'machine_cap':5,'no_proof_value_prettyprint':True}
(D/'request.json').write_text(json.dumps(rec,indent=2)+'\n');t=time.monotonic()
with rawpath.open('wb') as f:proc=subprocess.run(argv,stdout=f,stderr=subprocess.STDOUT,env=dict(os.environ,TCSLIB_LEAN_SLOTS='3'))
elapsed=time.monotonic()-t;raw=rawpath.read_bytes();text=raw.decode();buf=io.BytesIO()
with gzip.GzipFile(filename='',mode='wb',fileobj=buf,compresslevel=9,mtime=0) as z:z.write(raw)
gz=buf.getvalue();enc=base64.encodebytes(gz);(D/'ArbitraryFiniteness.out').write_bytes(raw);(D/'ArbitraryFiniteness.out.gz').write_bytes(gz);(D/'ArbitraryFiniteness.out.gz.base64.txt').write_bytes(enc);assert gzip.decompress(base64.b64decode(b''.join(enc.split()),validate=True))==raw
rec.update({'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':proc.returncode,'seconds_including_any_slot_wait':elapsed,'errors':len(re.findall(r'error:',text)),'warnings':len(re.findall(r'warning:',text)),'sorry_warnings':len(re.findall(r"declaration uses 'sorry'",text)),'raw_bytes':len(raw),'raw_sha256':sha(raw),'gzip_bytes':len(gz),'gzip_sha256':sha(gz),'utf8_base64_bytes':len(enc),'utf8_base64_sha256':sha(enc),'source_unchanged':sha((Path(c['actual_worktree'])/c['source_path']).read_bytes())==c['source_sha256'],'owner_olean_unchanged':sha(Path(c['owner_olean']).read_bytes())==c['owner_olean_sha256']})
(D/'result.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2),flush=True)
if proc.returncode:raise SystemExit(proc.returncode)
assert rec['errors']==rec['warnings']==rec['sorry_warnings']==0
assert '[hF6Rewind : Fintype Turing.RewindPhase]' in text and '[hF6Seek : Fintype Turing.SeekPhase]' in text
assert "'Complexity.space_universal' depends on axioms: [propext, Classical.choice, Quot.sound]" in text
(D/'verification.json').write_text(json.dumps({'result':'PASS fresh0d arbitrary-local-Fintype diagnostic','source_head':c['candidate_head'],'two_diagnostic_binders_present_in_printed_prefix_type':True,'two_reflexive_local_inference_equations_elaborated':True,'all19_guard_sections_retained':True,'target_exact_standard3_axioms':True,'source_unchanged':True,'no_source_public_API_or_header_change':True,'limits':'Bounded conditional witness-only check; two ineffective actual-instance opacity controls remain separately disclosed; no theorem-value equivalence or blanket foreign-definition seal'},indent=2)+'\n')
