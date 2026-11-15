"""Serial seal checks, complete raw logs, diagnostic mapping, and slot-free fairness gaps."""
from pathlib import Path
import subprocess,sys,json,time,re
plan=Path(sys.argv[1]);out=Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
for r in json.loads(plan.read_text()):
 print('SEAL START',r['label'],flush=True)
 p=subprocess.run([sys.executable,'-I','evidence/tools/check_one.py',r['module'],r['label'],str(out)])
 record=json.loads(Path(r['record']).read_text());log=out/(r['label']+'.log')
 raw=log.read_text();line_map={x['probe_line']:x['source_line'] for x in record['source_to_probe_lines']}
 src=subprocess.check_output(['git','show',record['rev']+':'+record['source']],text=True).splitlines()
 ns=[];decl=[]
 for i,l in enumerate(src,1):
  m=re.match(r'^namespace\s+(\S+)',l)
  if m:ns.append(m[1])
  m=re.match(r'^(?:(?:private|noncomputable|protected|nonrec)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s(:{\[]+)',l)
  if m:decl.append((i,'.'.join(ns+[m[1]])))
  if re.match(r'^end\b',l) and ns:ns.pop()
 errors=[]
 for m in re.finditer(r'^\S+\.lean:(\d+):(\d+): error[:(]',raw,re.M):
  line=line_map.get(int(m[1]));name=next((n for i,n in reversed(decl) if line is not None and i<=line),'HARNESS')
  errors.append({'probe_line':int(m[1]),'source_line':line,'declaration':name})
 result=dict(r,exit=p.returncode,errors=errors,failing_declarations=sorted({x['declaration'] for x in errors}))
 (out/(r['label']+'.attribution.json')).write_text(json.dumps(result,indent=2)+'\n')
 with (out/'attributed-results.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
 subprocess.run([sys.executable,'-I','evidence/tools/rule10/verify_guards.py','--record',r['record'],'--log',str(log),'--out',str(out/(r['label']+'.guards.json'))],check=True)
 print('SEAL END',r['label'],'errors',len(errors),flush=True)
 if any(e['declaration']=='HARNESS' for e in errors):raise SystemExit('Harness diagnostic: stop and inspect')
 time.sleep(6)
