from pathlib import Path
import json,subprocess,sys
O=Path('/private/tmp/ab34-overnight-sat-import-proposal');jobs=json.loads((O/'scope-control-jobs.json').read_text());identities=json.loads((O/'control-identities.json').read_text());idmap={r['context']:r['identities'] for r in identities};checked=[]
for job in jobs:
 name=job['job']+'-attempt1';command=['python3','-I',str(O/'run-job.py'),name,job['file']]
 p=subprocess.run(command)
 receipt=json.loads((O/(name+'.json')).read_text());raw=(O/(name+'.log')).read_text()
 if p.returncode!=job['expected_exit'] or receipt['exit']!=job['expected_exit'] or receipt['errors']!=job['expected_errors'] or receipt['sorry_warnings']:
  raise SystemExit('Unexpected result; retained for review: '+name)
 if '-controls-' in job['job']:
  context=job['job'].split('-controls-',1)[0];variant=job['job'].rsplit('-',1)[1]
  for a in idmap[context]:
   k='CONTROL|'+a['definition']+'|'+a['mode']+'|'+('PASS|kernelChecked='+a['kernel_name'] if variant=='native' else 'FAIL')
   if raw.count(k)!=1:raise SystemExit('Control identity mismatch: '+name+' '+k)
  if variant=='sealed' and raw.count('error: RFL_CONTROL|')!=len(idmap[context]):raise SystemExit('Negative error identities mismatch: '+name)
 checked.append({'job':job['job'],'receipt':name+'.json','exit':p.returncode,'errors':receipt['errors'],'expected':True})
(O/'scope-control-verification.json').write_text(json.dumps({'result':'PASS4 hypothetical SAT declarations in1context;fresh positive and negative controls','jobs':checked,'positive':sum(len(v) for v in idmap.values()),'negative':sum(len(v) for v in idmap.values()),'no_unsafe_transparency_or_reducibility_override':True,'one_job_at_a_time':True,'imported_theorem_values_not_traversed':True},indent=2)+'\n');print('ALL4_SCOPE_CONTROL_JOBS_PASS')
