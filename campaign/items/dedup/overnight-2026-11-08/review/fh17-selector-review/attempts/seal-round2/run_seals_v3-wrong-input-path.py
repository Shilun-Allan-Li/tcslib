from pathlib import Path
import json,os,subprocess,time,datetime,hashlib,re
O=Path(__file__).parent
T=json.loads((O/'TASK.json').read_text())
W=Path(T['source_worktree'])
P=O/'live/project-v3'
S=Path(os.environ['TCSLIB_SCRATCH'])
old=json.loads((O/'attempts/seal-round2/SEAL-RESULTS-v3.json').read_text())
prior={(d['label'],d['kind']):d for d in old}
rows=json.loads((O/'SEAL-INPUTS-v3.json').read_text())
out=O/'seal-runs-v3'
out.mkdir(exist_ok=True)
results=[]
for d in rows:
    file=Path(d['input'])
    assert hashlib.sha256(file.read_bytes()).hexdigest()==d['input_sha256']
    before=prior.get((d['label'],d['kind']))
    if before is not None and before['input_sha256']==d['input_sha256']:
        result=dict(before)
        result['reused_actual_prior_input_code_exact']=True
        result['final_input_v3']=d
        result['actual_record']=before.get('actual_record', 'seal-runs-v2/'+d['label']+'-'+d['kind']+'.json')
    else:
        argv=['bash',str(W/'devtools/seyoon/leanelab.sh'),str(P),str(S/'oleans-mac8'),str(file)]
        st=datetime.datetime.now(datetime.timezone.utc).isoformat()
        tm=time.monotonic()
        r=subprocess.run(argv,cwd=P,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        raw=r.stdout
        name=d['label']+'-'+d['kind']
        (out/(name+'.out')).write_bytes(raw)
        errors=len(re.findall(r': error(?:\([^\n]*?\))?:',raw.decode(errors='replace')))
        result=d|{'argv':argv,'start_utc':st,'seconds':time.monotonic()-tm,'exit':r.returncode,'errors':errors,'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'output_sha256':hashlib.sha256(raw).hexdigest(),'output_bytes':len(raw),'output_file':'seal-runs-v3/'+name+'.out','one_own_Lean_at_a_time':True,'actual_executed':True,'PASS':r.returncode==0 and errors==0,'reused_actual_prior_input_code_exact':False}
        (out/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
    results.append(result)
    (O/'SEAL-RESULTS-v3.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['label','kind','exit','errors','PASS','reused_actual_prior_input_code_exact']}),flush=True)
