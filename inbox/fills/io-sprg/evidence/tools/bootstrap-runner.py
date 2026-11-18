# io-sprg serial foreground module runner; every module holds one host Lean slot.
import datetime, hashlib, json, os, pathlib, re, subprocess, sys
root=pathlib.Path.cwd()
order=pathlib.Path(sys.argv[1]); folder=pathlib.Path(sys.argv[2]);folder.mkdir(parents=True,exist_ok=True)
(folder/'mods').mkdir(exist_ok=True)
env=dict(os.environ);env['LEAN_SLOT_TAG']='io-sprg'
env['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+env['PATH']
env['TCSLIB_OLEANS']=str(root/'.lake/io-sprg-oleans')
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
(folder/'HEAD-at-start.txt').write_text(head+'\n')
mods=order.read_text().splitlines()
with (folder/'results.jsonl').open('a') as results:
  for m in mods:
    log=folder/'mods'/(m.replace('/','_')+'.log')
    stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
    sha=hashlib.sha256((root/(m+'.lean')).read_bytes()).hexdigest()
    print(stamp+' START '+m,flush=True)
    (folder/'current-module.txt').write_text(m+'\n')
    with log.open('w') as out:
      out.write(stamp+' START '+m+'\n');out.flush()
      cmd=['/private/tmp/io-sprg-tools/lean-slot.sh','/usr/bin/time','-l',
           'bash','scripts/lean_check_tree.sh',m]
      proc=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env)
      (folder/'current-wrapper.pid').write_text(str(proc.pid)+'\n')
      rc=proc.wait()
      end=datetime.datetime.now(datetime.timezone.utc).isoformat()
      out.write(end+f' END rc={rc}\n')
    txt=log.read_text()
    errors=len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]',txt,re.M))
    generic=len(re.findall(r'error[:(]',txt))
    olean=root/'.lake/io-sprg-oleans'/(m+'.olean')
    rec=dict(module=m,rc=rc,errors=errors,error_forms=generic,start=stamp,end=end,
      source_sha256=sha,head_at_start=head,log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
      object_sha256=hashlib.sha256(olean.read_bytes()).hexdigest() if olean.exists() else None)
    results.write(json.dumps(rec)+'\n');results.flush()
    print(end+f' END rc={rc} errors={errors}/{generic} '+m,flush=True)
    if rc or errors or generic: sys.exit(1)
print('ALL_MODULES_PASS '+str(len(mods)),flush=True)
