"""Integrate one reviewed exact-header proof, check it, and restore on failure."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys
file=Path(sys.argv[1]);scope=sys.argv[2];frag=Path(sys.argv[3]).read_text();tag=sys.argv[4];name=scope+'.nonterminal'
before=file.read_text();start=before.index('theorem '+scope);a=before.index('\n  | cast k =>',start)+1;b=before.index('\nend PartialGarbling.PrefixAlgebra',a)
assert before[a:b].count('sorry')==1
f=frag.index('  | cast k =>');file.write_text(before[:a]+frag[f:].rstrip()+'\n'+before[b:])
root=Path.cwd();env=dict(os.environ,LEAN_SLOT_TAG='io-phfe',TCSLIB_OLEANS=str(root/'.lake/io-phfe-oleans'));env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH'];base_ev=Path('evidence/logs/proof-steps')/tag;attempt=1
while (base_ev/f'attempt-{attempt}').exists():attempt+=1
ev=base_ev/f'attempt-{attempt}';ev.mkdir(parents=True)
def check(label):
 raw=file.read_bytes();log=ev/(label+'.log')
 (ev/(label+'.lean.txt')).write_bytes(raw)
 with log.open('w') as out:
  out.write(f'file={file}\nsource_sha256={hashlib.sha256(raw).hexdigest()}\nworking_source_development_check=True\n');out.flush()
  p=subprocess.run(['bash','evidence/preparation/lean-slot.sh','/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',str(file)[:-5]],env=env,stdout=out,stderr=subprocess.STDOUT)
 s=log.read_text();n=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]',s,re.M));r={'file':str(file),'name':name,'label':label,'rc':p.returncode,'both_error_forms':n,'sha256':hashlib.sha256(raw).hexdigest()};(ev/(label+'.json')).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True);return not(p.returncode or n),s
ok,log=check('candidate')
if not ok:
 file.write_text(before);restored,_=check('restore');assert restored
 print(log[-11000:],flush=True);raise SystemExit(1)
print('PROOF_STEP_PASS',name,flush=True)
