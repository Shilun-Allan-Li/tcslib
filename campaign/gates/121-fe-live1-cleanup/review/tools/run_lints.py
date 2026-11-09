from pathlib import Path
import subprocess,sys,json,hashlib,datetime,time,os
B=Path(__file__).resolve().parents[1];config=json.loads((B/'qa/config.json').read_text());files=config['changed_current_owners'];O=B/'qa/lints';O.mkdir()
records=[]
for phase in ['BASE','HEAD']:
 root=Path(config[phase+'_export'])
 for kind in ['campaign-check8b','style']:
  if kind=='campaign-check8b':cmd=[sys.executable,'-I',str(B/'tools/targeted_campaign_lint.py'),str(root),'--check8b',*files]
  else:cmd=[sys.executable,'-I',str(root/'scripts/style_lint.py'),*files]
  source={p:hashlib.sha256((root/p).read_bytes()).hexdigest()for p in files}
  start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();r=subprocess.run(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  out=O/(phase+'-'+kind+'.out');err=O/(phase+'-'+kind+'.err');out.write_bytes(r.stdout);err.write_bytes(r.stderr)
  row={'phase':phase,'kind':kind,'start_utc':start,'end_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seconds':time.monotonic()-t,'command':cmd,'cwd':str(root),'exit':r.returncode,'stdout':str(out.relative_to(B)),'stderr':str(err.relative_to(B)),'stdout_sha256':hashlib.sha256(r.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(r.stderr).hexdigest(),'source_SHA256_before':source,'source_unchanged':source=={p:hashlib.sha256((root/p).read_bytes()).hexdigest()for p in files},'scope':'Exactly four current owners; canonical check_file/check_facade via retained adapter for campaign lint, canonical CLI for style lint; no screen or Lean invoked'}
  assert row['source_unchanged'];(O/(phase+'-'+kind+'-receipt.json')).write_text(json.dumps(row,indent=2)+'\n');records.append(row);print(json.dumps({'phase':phase,'kind':kind,'exit':r.returncode,'seconds':row['seconds']}),flush=True)
(B/'qa/lints/RUNS.json').write_text(json.dumps(records,indent=2)+'\n')
