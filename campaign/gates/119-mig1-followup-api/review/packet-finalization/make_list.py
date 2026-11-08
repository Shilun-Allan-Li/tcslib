"""Complete uncapped UTF8 candidate input selection, not staging or publication."""
from pathlib import Path
import base64,datetime,gzip,hashlib,json,os,subprocess
out=Path(__file__).resolve().parent;root=out.parents[4];gate=root/'campaign/gates/119-mig1-followup-api';head='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');H=lambda b:hashlib.sha256(b).hexdigest()
fixed=['AGENTS.md','policy.md','workflow.md','campaign/maintainer/START-HERE.md','campaign/maintainer/WORKFLOW.md','campaign/maintainer/HANDOFF.md','campaign/standards/TEMPLATE.md','campaign/standards/fill-environment-addendum.md','campaign/duplication-ledger.md','machine-library-design.md','lean-toolchain','lakefile.lean','lake-manifest.json','devtools/seyoon/leanelab.sh','devtools/seyoon/leanelab-o.sh','scripts/lean_check_tree.sh','devtools/seyoon/mk-next.sh','devtools/seyoon/mkdownmulti.py','devtools/seyoon/mkreplay.py','devtools/seyoon/scratch-api/slotrun.sh','devtools/seyoon/scratch-api/staticsorry.py','devtools/seyoon/scratch-api/env.sh.example','scripts/copy-text-screen-v3.py','scripts/campaign_style_lint.py','scripts/style_lint.py']
selected=set(fixed);pop=(gate/'review/source-lint-screen/population.txt').read_text().splitlines();assert len(pop)==16;selected.update(pop)
excluded=[]
for f in gate.rglob('*'):
 if not f.is_file() or '__pycache__' in f.parts:continue
 if out in f.parents and f.name in ['BUNDLE-FILES.candidate.txt','candidate-input-review.json','MANIFEST.json','SHA256SUMS']:continue
 rel=str(f.relative_to(root))
 if f.suffix=='.gz':excluded.append(rel);continue
 f.read_bytes().decode('utf-8');selected.add(rel)
assert set(excluded)=={'campaign/gates/119-mig1-followup-api/review/compiled-comparison/Inventory-base.out.gz','campaign/gates/119-mig1-followup-api/review/compiled-comparison/Inventory-head.out.gz'}
for r in json.loads((gate/'review/compiled-comparison/utf8-archives-verification.json').read_text())['archives']:
 b=(gate/'review/compiled-comparison'/r['utf8_file']).read_bytes();z=base64.b64decode(b''.join(b.split()),validate=True);raw=gzip.decompress(z)
 assert (len(b),H(b))==(r['utf8_bytes'],r['utf8_sha256']) and (len(z),H(z))==(r['gzip_bytes'],r['gzip_sha256']) and (len(raw),H(raw))==(r['raw_stdout_stderr_bytes'],r['raw_stdout_stderr_sha256'])
 assert str((gate/'review/compiled-comparison'/r['utf8_file']).relative_to(root)) in selected
required=['evidence/replay-mfup2/receipt.json','evidence/replay-mfup2/replay-mfup2.log','evidence/replay-mfup2/replay-mfup2-static.txt','evidence/replay-mfup2/replay-mfup2-launches.log','evidence/replay-mfup2/actual-branch-lean_check_tree.sh','evidence/replay-mfup2/effective-pipeline.json','evidence/replay/partial-mfup1/receipt.json','review/source-lint-screen/final-verification.json','review/source-lint-screen/new-candidate-classification.json','review/compiled-comparison/Base.out.gz.base64.txt','review/compiled-comparison/Head.out.gz.base64.txt','review/packet-finalization/pack.md','review/packet-finalization/source-linkage.json','review/packet-finalization/final-evidence-verification.json','review/packet-finalization/tool-provenance.json']
assert all(str((gate/f).relative_to(root)) in selected for f in required)
rows=[]
for rel in sorted(selected):
 if rel.startswith('TCSlib/'):
  b=subprocess.run(['git','-C',str(root),'show',head+':'+rel],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env).stdout;pin=head
 else:b=(root/rel).read_bytes();pin='Records bytes at candidate capture; root supplies immutable records pin in external prologue/prompt after commit'
 b.decode('utf-8');assert b'\x00' not in b,rel
 rows.append({'path':rel,'bytes':len(b),'sha256':H(b),'origin':pin})
assert all(str((gate/'review/source-lint-screen/inputs'/s/(f+'.txt')).relative_to(root)) in selected for s in ['base','head'] for f in pop)
assert not list(out.rglob('*.lean'))
(out/'BUNDLE-FILES.candidate.txt').write_text('\n'.join(sorted(selected))+'\n')
review={'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Final candidate selection for root review/canonical-pack copy and committed-pin staging; no dispatch/gate closure or merge clearance','source_head':head,'files':len(rows),'total_input_bytes':sum(r['bytes'] for r in rows),'uncapped':True,'all_selected_inputs_exist_UTF8_no_NUL':True,'full16_current_sources_and32_archived_sides':True,'all_existing_gate_evidence_and_review_UTF8_included':True,'full401_replay_and_partial272_history_included':True,'six_final_material_screen_rows_included':True,'binary_gzip_excluded_only_with_complete_verified_lossless_UTF8_representations':excluded,'no_running_result_predicted_or_truncated':True,'no_untracked_active_lean_file_in_output':True,'root_finalization':'Root copies candidate pack to canonical location, refreshes list/status at records commit and stages/verifies immutable bundle/prologue/prompt; no self-referential records/bundle placeholder is in finalpack.','input_rows':rows}
(out/'candidate-input-review.json').write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps({k:v for k,v in review.items() if k!='input_rows'},indent=2))
