"""Pin existing effective controls and prove defining source data unchanged in the new context."""
from pathlib import Path
import sys,importlib.util,json,re,hashlib
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4];prior=out.parent/'review-forward-rewind-factoring';H=lambda b:hashlib.sha256(b.encode() if isinstance(b,str) else b).hexdigest();defs=json.loads((out/'seal-manifest.json').read_text())['definitions']
spec=importlib.util.spec_from_file_location('P',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
base=out.parent/'screen-current25-draft/inputs/head';files=(out.parent/'review-final-source/screen-population-final-review.txt').read_text().splitlines();wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-epad');indexes=[]
for stage in ['prior_context','current']:
 index={}
 for f in files:
  path=base/(f+'.txt') if stage=='prior_context' else wt/f;s=path.read_text()
  for d in P.decls(s):
   if d['name'] not in defs:continue
   raw=d['raw'];m=re.search(r'(?m)^/(?:--|-!)',raw)
   if m:raw=raw[:m.start()]
   assert d['name'] not in index
   index[d['name']]={'name':d['name'],'owner':f,'kind':d['kind'],'code':P.norm(P.clean(raw)),'definition_source_sha256':H(P.norm(P.clean(raw)))}
 assert set(index)==set(defs),(stage,set(defs)-set(index));indexes.append(index)
rows=[]
for n in defs:
 a,b=indexes[0][n],indexes[1][n];assert a==b,(n,a['owner'],b['owner']);rows.append({'name':n,'owner':b['owner'],'kind':b['kind'],'normalized_full_declaration_sha256':b['definition_source_sha256'],'type_data_body_unchanged':True})
# Actual complete context before/data are related by recorded proof/comment-only source changes.
source_provenance={'baseline':'screen-current25-draft/inputs/head (current2 pre-comment capture)','baseline_capture_receipt_sha256':H((out.parent/'screen-current25-draft/capture.json').read_bytes()),'phase2_literal_header_and_runtime_freeze_sha256':H((out.parent/'review-final-source-phase2/freeze-summary.json').read_bytes()),'read_only_complete_current3_context':str(wt.parent/'oleans-mig1-preflight-current3')}
copydir=out/'reused-controls';copydir.mkdir(exist_ok=True);copied=[]
for stem in ['Controls37-unsealed-v1','Controls37-sealed-v1']:
 receipt=json.loads((prior/(stem+'-run.json')).read_text());assert receipt['input_sha256']==H((prior/(stem+'.lean.txt')).read_bytes()) and receipt['output_sha256']==H((prior/(stem+'.out')).read_bytes())
 assert receipt['exit']==(0 if 'unsealed' in stem else 1) and receipt['errors']==(0 if 'unsealed' in stem else 74)
 for suffix in ['.lean.txt','.out','-run.json']:
  name=stem+suffix;b=(prior/name).read_bytes();(copydir/name).write_bytes(b);copied.append({'source':str((prior/name).relative_to(root)),'copy':str((copydir/name).relative_to(out)),'sha256':H(b)})
coverage=json.loads((prior/'control-coverage.json').read_text());assert coverage['pairs']==37 and coverage['goals']==74 and coverage['one_rfl_error_per_goal'] and coverage['synthetic_duplicate_drop']['rejected'];assert coverage['definition_order_matches_existing_effective_control_template']==defs
b=(prior/'control-coverage.json').read_bytes();(copydir/'control-coverage.json').write_bytes(b);copied.append({'source':str((prior/'control-coverage.json').relative_to(root)),'copy':'reused-controls/control-coverage.json','sha256':H(b)})
result={'fresh_Lean_control_runs_this_prototype':0,'reuse_exact_scope':'All37 ordinary definition controls, including the12-or-fewer reached here; originally74pointwise/abstracted goals calibrated in read-only complete current2. No new definition or definition body/type/ownership in current3 for these37.','37_defining_declarations_identical':True,'definition_identity_rows':rows,'source_context_provenance':source_provenance,'actual_prior_results':{'unsealed_goals_passed':74,'sealed_intended_rfl_failures':74,'per_goal_multiplicity_verified':True,'synthetic_duplicate_drop_rejected':True},'copied_evidence':copied,'limitation':'These calibration runs are attributed to the preceding forward-rewind review, not claimed rerun in current3; current3 has changed proof/comment artifacts but identical37defining statements/data/bodies.'}
(out/'control-reuse.json').write_text(json.dumps(result,indent=2)+'\n');print('Verified identical37definitionhomes/types/data/bodies; pinned7priorcontrolartifacts; no controls rerun.')
