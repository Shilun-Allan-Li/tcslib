import datetime, hashlib, json, pathlib, subprocess, sys
root=pathlib.Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
evidence=pathlib.Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
module, attempt=sys.argv[1:]
log=evidence/'logs/helper-checks'/f'{pathlib.Path(module).name}-{attempt}.log'
command=['python3','-I',str(evidence/'tools/lean_host_guard.py'),'--',
         '/usr/bin/time','-l','/bin/bash','scripts/lean_check_tree.sh',module]
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
source=(root/(module+'.lean')).read_bytes()
log.with_suffix('.source.lean').write_bytes(source)
with log.open('w') as f:
 f.write('start='+started+'\ncommand='+json.dumps(command)+'\nsource-sha256='+hashlib.sha256(source).hexdigest()+'\n');f.flush()
 p=subprocess.run(command,cwd=root,stdout=f,stderr=subprocess.STDOUT)
 ended=datetime.datetime.now(datetime.timezone.utc).isoformat()
 f.write('end='+ended+'\nexit='+str(p.returncode)+'\n')
row=dict(module=module,attempt=attempt,start=started,end=ended,exit=p.returncode,log=str(log.relative_to(evidence)),source_sha256=hashlib.sha256(source).hexdigest())
with (evidence/'logs/helper-checks/results.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(log.read_text());sys.exit(p.returncode)
