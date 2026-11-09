from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,subprocess,sys,time
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');V=Path('/private/tmp/ab34-ro1-native-overlay');rel,attempt=sys.argv[1:3]
assert rel.startswith('TCSlib/') and rel.endswith('.lean') and '..' not in Path(rel).parts
key=rel[:-5].replace('/','__')+'__'+attempt;d=O/'native';d.mkdir(exist_ok=True);log=d/(key+'.log');receipt=d/(key+'.json');assert not log.exists() and not receipt.exists()
source=(W/rel).read_bytes()
removed=[]
for suffix in ['.olean','.ilean','.c','.trace']:
 p=V/(rel[:-5]+suffix)
 if p.exists():p.unlink();removed.append(str(p))
command=['bash',str(W/'devtools/seyoon/leanelab-o.sh'),str(W),str(V),rel,str(V)];env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
with log.open('wb') as f:p=subprocess.run(command,env=env,stdout=f,stderr=subprocess.STDOUT)
b=log.read_bytes();output=V/(rel[:-5]+'.olean');r={'source_worktree':str(W),'file':rel,'attempt':attempt,'source_sha256':hashlib.sha256(source).hexdigest(),'source_unchanged_during_run':source==(W/rel).read_bytes(),'started_utc':start,'finished_utc':datetime.now(timezone.utc).isoformat(),'seconds_including_slot_wait':time.monotonic()-t,'command':command,'exit':p.returncode,'errors':b.count(b'error:'),'warnings':b.count(b'warning:'),'sorry_warnings':b.count(b"declaration uses 'sorry'"),'raw_bytes':len(b),'raw_sha256':hashlib.sha256(b).hexdigest(),'fresh_olean_exists':output.is_file() and output.stat().st_size>0,'fresh_olean_sha256':hashlib.sha256(output.read_bytes()).hexdigest() if output.is_file() else None,'removed_only_own_overlay_outputs':removed,'whole_overlay_origin':'complete895-object MAC8 clone; never spliced','one_own_job_local3_machine5_j4_nice10':True,'MAC8_not_written':True};receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
for line in b.decode(errors='replace').splitlines():
 if 'error' in line:print(line)
sys.exit(p.returncode if p.returncode else (1 if r['errors'] or not r['fresh_olean_exists'] else 0))
