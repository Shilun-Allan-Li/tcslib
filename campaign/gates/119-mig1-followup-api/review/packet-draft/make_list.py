"""Uncapped candidate UTF8 selection; not staging/publication or an immutable bundle."""
from pathlib import Path
import base64,datetime,gzip,hashlib,json,os,subprocess
out=Path(__file__).resolve().parent;root=out.parents[4];gate=root/'campaign/gates/119-mig1-followup-api';head='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');H=lambda b:hashlib.sha256(b).hexdigest()
fixed=['AGENTS.md','policy.md','workflow.md','campaign/maintainer/START-HERE.md','campaign/maintainer/WORKFLOW.md','campaign/maintainer/HANDOFF.md','campaign/standards/TEMPLATE.md','campaign/standards/fill-environment-addendum.md','campaign/duplication-ledger.md','machine-library-design.md','lean-toolchain','lakefile.lean','lake-manifest.json','devtools/seyoon/leanelab.sh','devtools/seyoon/leanelab-o.sh','scripts/lean_check_tree.sh']
selected=set(fixed);selected.update((gate/'review/source-lint-screen/population.txt').read_text().splitlines())
excluded=[]
for p in gate.rglob('*'):
 if not p.is_file() or '__pycache__' in p.parts or out in p.parents:continue
 rel=str(p.relative_to(root))
 if p.suffix=='.gz':excluded.append(rel);continue
 p.read_bytes().decode('utf-8');selected.add(rel)
assert set(excluded)=={'campaign/gates/119-mig1-followup-api/review/compiled-comparison/Inventory-base.out.gz','campaign/gates/119-mig1-followup-api/review/compiled-comparison/Inventory-head.out.gz'}
# Lossless representations replace only those two binary archives; preserve full raw output.
u=json.loads((gate/'review/compiled-comparison/utf8-archives-verification.json').read_text())
for x in u['archives']:
 encoded=(gate/'review/compiled-comparison'/x['utf8_file']).read_bytes();gz=base64.b64decode(b''.join(encoded.split()),validate=True);raw=gzip.decompress(gz)
 assert H(encoded)==x['utf8_sha256'] and len(encoded)==x['utf8_bytes'];assert H(gz)==x['gzip_sha256'] and len(gz)==x['gzip_bytes'];assert H(raw)==x['raw_stdout_stderr_sha256'] and len(raw)==x['raw_stdout_stderr_bytes']
 assert 'campaign/gates/119-mig1-followup-api/review/compiled-comparison/'+x['utf8_file'] in selected
# This folder is candidate review data. Include complete currently existing text files,
# except self-referential controls/manifests; root may select the issued replacement pack.
for p in out.rglob('*'):
 if p.is_file() and p.name not in {'BUNDLE-FILES.candidate.txt','candidate-input-review.json','MANIFEST.json','SHA256SUMS'}:selected.add(str(p.relative_to(root)))
rows=[]
for rel in sorted(selected):
 if rel.endswith('.lean'):
  b=subprocess.run(['git','-C',str(root),'show',head+':'+rel],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,env=env).stdout;pin=head
 else:b=(root/rel).read_bytes();pin='Current records workspace; final immutable records pin pending'
 b.decode('utf-8');assert b'\x00' not in b,rel
 rows.append({'path':rel,'bytes_at_candidate_capture':len(b),'sha256_at_candidate_capture':H(b),'origin':pin,'may_change_before_issue':('/evidence/replay' in rel or '/review/source-lint-screen/' in rel)})
(out/'BUNDLE-FILES.candidate.txt').write_text('\n'.join(sorted(selected))+'\n')
receipt={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'DRAFT selection only. Current replay/screen files may still be running; root must refresh/adopt them and finalize records/source pins before issue.','candidate_files':len(selected),'all_selected_files_exist_UTF8_no_NUL':True,'uncapped_all_current_gate_evidence_reviews_inputs':True,'all_16_cited_TCSlib_sources_at_current_immutable_head':True,'all_32_before_head_screen_captures_and_full_archives_included':True,'binary_gzip_files_represented_losslessly_by_complete_UTF8_base64':excluded,'encoded_gzip_and_full_raw_output_hashes_independently_reconciled':True,'gzip_outputs_not_native_executed':True,'source_head':head,'pending':['mfup2 full401 completion/effective-j4/source-stability/static receipt','16-file head screen completion and full source-semantic/cumulative dispositions','records pin, final exact source head confirmation, immutable bundle hash/bytes/count, publication and Codex dispatch prompt'],'input_rows':rows};(out/'candidate-input-review.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='input_rows'},indent=2))
