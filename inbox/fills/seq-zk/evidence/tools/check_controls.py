"""Run and audit each paired native-name sensitivity control through the host wrapper."""
from pathlib import Path
import subprocess,sys,json,hashlib,re,time
planpath,outpath=sys.argv[1:3];planpath=Path(planpath);out=Path(outpath);out.mkdir(parents=True,exist_ok=True)
plan=json.loads(planpath.read_text());audits=[]
for index,row in enumerate((r for r in plan if 'module' in r),1):
 label='checkpoint2-control-'+str(index).zfill(2)
 p=subprocess.run([sys.executable,'-I','evidence/tools/check_one.py',row['module'],label,str(out)])
 rawpath=out/(label+'.log');raw=rawpath.read_text()
 errors=[{'line':int(m[1]),'column':int(m[2])} for m in re.finditer(r'^\S+\.lean:(\d+):(\d+): error[:(]',raw,re.M)]
 expected=row['expected_error_count']
 assert len(errors)==expected,(row,errors)
 assert (p.returncode==0)==(expected==0),(row,p.returncode)
 if expected:assert errors[0]['line']==row['negative_start_line'],(row,errors)
 source=Path(row['module']+'.lean');assert hashlib.sha256(source.read_bytes()).hexdigest()==row['source_sha256']
 result=dict(row,label=label,exit=p.returncode,errors=errors,raw_log=str(rawpath),expectation_passed=True)
 if row['sealed']:
  ownerpath=planpath.parent/('seal-'+row['variant'])/(row['request_record']+'.json')
  owner=json.loads(ownerpath.read_text());rows=[r for r in owner['rows'] if r['spelling'] in row['request_names']]
  assert len(rows)==1
  req=out/(label+'.requests.json');req.write_text(json.dumps(dict(rows=rows,requested=1),indent=2)+'\n')
  subprocess.run([sys.executable,'-I','evidence/tools/rule10/verify_guards.py','--record',str(req),'--log',str(rawpath),'--out',str(out/(label+'.guards.json'))],check=True)
 with (out/'control-results.jsonl').open('a') as f:f.write(json.dumps(result)+'\n')
 audits.append(result);print('CONTROL EXPECTATION PASS',label,row['target'],'sealed='+str(row['sealed']),flush=True)
 time.sleep(6)
summary=dict(probes=len(audits),unsealed=sum(not r['sealed'] for r in audits),sealed_each_exactly_one_error=sum(r['sealed'] for r in audits),all_expectations_and_native_guards_passed=True)
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary,flush=True)
