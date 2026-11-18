"""Integrate one term proof at a time, checking and stopping/reverting on the first failure."""
from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys
root=Path.cwd();file=Path('TCSlib/Cryptography/Pairing/Exponents.lean');module=file.as_posix()[:-5]
drafts=Path('/private/tmp/io-phfe-drafts/proofs-pairing');ev=Path('evidence/logs/proofs-exponents');ev.mkdir(exist_ok=True)
source_head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();env=dict(os.environ,LEAN_SLOT_TAG='io-phfe',TCSLIB_OLEANS=str(root/'.lake/io-phfe-oleans'));env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
rows=[r for r in json.loads(Path('evidence/statements/direct-admissions.json').read_text()) if r['file']==file.as_posix()]
proofs=[]
for row in rows:
 name=row['name'].split('.')[-1];frag=(drafts/(name+'.proof.lean.inc')).read_text();m=re.search(r'^theorem '+re.escape(name)+r'\b',frag,re.M);assert m,name
 e=frag.index(' :=',m.start());proofs.append((name,frag[m.start():e],frag[e:].rstrip()))

def check(name,label):
 raw=file.read_bytes();sha=hashlib.sha256(raw).hexdigest();path=ev/(name+'-'+label+'.log')
    if path.exists():
        serial=1
        while (ev/(name+'-'+label+f'-prior-{serial}.log')).exists():serial+=1
        path.rename(ev/(name+'-'+label+f'-prior-{serial}.log'))
    start=str(datetime.datetime.now(datetime.timezone.utc))
 with path.open('w') as log:
  log.write(f'development_source_head={source_head}\nsource_sha256={sha}\nsource_working_bytes_may_differ_from_head=True\nstart={start}\n');log.flush()
  p=subprocess.run(['bash','evidence/preparation/lean-slot.sh','/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',module],env=env,stdout=log,stderr=subprocess.STDOUT)
  log.write('rc='+str(p.returncode)+'\n')
 text=path.read_text();a=len(re.findall(r'^\S+\.lean:\d+:\d+: error:',text,re.M));b=len(re.findall(r'^\S+\.lean:\d+:\d+: error\(',text,re.M))
 rec={'name':name,'label':label,'rc':p.returncode,'errors_colon':a,'errors_paren':b,'source_sha256':sha,'log':str(path)}
 with (ev/'results.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return not(p.returncode or a or b),text

for name,header,body in proofs:
 before=file.read_text();m=re.search(r'^theorem '+re.escape(name)+r'\b',before,re.M);e=before.index(' :=',m.start());assert before[m.start():e]==header,'frozen header differs: '+name
 if not before[e:].startswith(' := sorry'):print('SKIP',name,'already filled',flush=True);continue
 after=before[:e]+body+before[e+len(' := sorry'):]
 if name=='groupDot_expVec':after=after.replace('**Proof sketch.** Induct over the finite index sum, using `pow_val_add`, `pow_val_mul` and\n`Finset.prod_pow_eq_pow_sum` to combine the powers.','**Proof sketch.** The local additive exponent homomorphism maps the finite sum to a\nproduct, giving `hSum`. The modular multiplication law gives `hCoordinate`; combine them\nwith the published product reader.')
 if name=='groupDot_expVecT':after=after.replace('**Proof sketch.** Combine `pow_val_add_GT` and `pow_val_mul_GT` over the finite index sum.','**Proof sketch.** The local target-group exponent homomorphism maps the finite sum to\na product, giving `hSum`. The modular multiplication law gives `hCoordinate`; combine\nthem with the published product reader.')
 file.write_text(after);print('CHECK',name,flush=True);ok,log=check(name,'candidate')
 if not ok:
  file.write_text(before);restored,_=check(name,'restore');assert restored,'restored source failed'
  print('FAILED_AND_RESTORED',name,flush=True);print(log[-9000:],flush=True);sys.exit(1)
 print('PASS',name,flush=True)
print('ALL_EXPONENT_TERM_PROOFS_PASS',flush=True)
