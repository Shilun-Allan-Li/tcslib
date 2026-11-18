# io-sprg immutable paired overlap-search record. No Lean.
import argparse,hashlib,json,shutil,re
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('name');ap.add_argument('--reuse',required=True);a=ap.parse_args();root=Path.cwd();home=root/'evidence/overlap';out=home/'probes'/a.name;out.mkdir(parents=True,exist_ok=True)
invalid=[]
records=[json.loads(l) for l in(home/'runs/results.jsonl').read_text().splitlines()];summary=[]
for mode in ['exact','apply']:
 module='/private/tmp/io-sprg-overlap/'+a.name+'-'+mode
 r=next(r for r in reversed(records) if r.get('module')==module)
 source=Path(module+'.lean');log=home/'runs/mods'/(module.replace('/','_')+'.log')
 assert hashlib.sha256(source.read_bytes()).hexdigest()==r['source_sha256']
 assert hashlib.sha256(log.read_bytes()).hexdigest()==r['log_sha256']
 shutil.copy2(source,out/(mode+'.lean.txt'));shutil.copy2(log,out/(mode+'.log'))
 status='CLOSED' if r['rc']==r['errors']==r['sorry']==0 else ('PARTIAL_NOT_PROOF' if mode=='apply' and r['rc']==r['errors']==0 and r['sorry'] else 'NO_CLOSING_PROOF' if '`exact?` could not close' in log.read_text() else 'DIAGNOSTIC_FAILURE')
 diagnostics=[l for l in log.read_text().splitlines() if re.match(r'^\S+\.lean:\d+:\d+: error[:(]',l)]
 bad=[l for l in diagnostics if not any(t in l for t in ('`exact?` could not close','apply? didn\'t find any relevant lemmas','maximum number of heartbeats','(deterministic) timeout'))]
 if bad:status='INVALID_ELABORATION'
 invalid.extend(dict(mode=mode,line=l) for l in bad)
 summary.append(dict(mode=mode,status=status,run=r,elaboration_errors=bad))
(out/'search.json').write_text(json.dumps(dict(goal=a.name,reused_api=a.reuse,qualification='Source imports exclude all StructuredSeed modules. Partial apply? suggestions and diagnostic sorry warnings are not proofs.',searches=summary),indent=1)+'\n')
with(root/'evidence/lean_proof/search_log.md').open('a') as f:f.write('\n'+a.name+': '+', '.join(r['mode']+'='+r['status'] for r in summary)+'. Reuse: '+a.reuse+'.\n')
assert not invalid,('Invalid overlap statement elaboration; repair and rerun a fresh probe before filling',invalid)
print('OVERLAP_RECORDED',a.name,[r['status'] for r in summary])
