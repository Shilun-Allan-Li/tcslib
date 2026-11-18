# Development driver: skips descendants of failed/missing dependencies and continues independent branches.
# Derived from the lead-authored bootstrap.py; all Lean invocations remain serial and source-bound.
from pathlib import Path
import datetime, hashlib, os, re, subprocess, sys
order_path, log_name = sys.argv[1:3]
failed=set()
root=Path.cwd(); tree=root/'.lake/io-phfe-oleans'
env=dict(os.environ)
env['PATH']=str(Path.home()/'.elan/bin')+':'+env['PATH']
env['LEAN_SLOT_TAG']='io-phfe'; env['TCSLIB_OLEANS']=str(tree)
logdir=root/'evidence/logs'/log_name; logdir.mkdir(parents=True,exist_ok=True)
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
mods=Path(order_path).read_text().splitlines()
with (logdir/'summary.tsv').open('w') as summary:
    summary.write('module\thead\tsource_sha256\tstart_utc\tend_utc\trc\terrors_colon\terrors_paren\tfresh_olean\n')
    summary.flush()
    for mod in mods:
        source=Path(mod+'.lean').read_bytes()
        assert source==subprocess.check_output(['git','show',head+':'+mod+'.lean']), 'source changed: '+mod
        imports=[l.split()[1].replace('.', '/') for l in source.decode().splitlines()
                 if l.startswith('import TCSlib')]
        unavailable=[d for d in imports if d in failed or not (tree/(d+'.olean')).is_file()]
        if unavailable:
            failed.add(mod)
            print('SKIP',mod,'unavailable',unavailable,flush=True)
            summary.write(f'{mod}\t{head}\tSKIP\t-\t-\t-2\t0\t0\tFalse\n'); summary.flush()
            continue
        sha=hashlib.sha256(source).hexdigest()
        start=datetime.datetime.now(datetime.timezone.utc).isoformat()
        path=logdir/(mod.replace('/','_')+'.log')
        print('START',mod,flush=True)
        with path.open('w') as log:
            log.write('head='+head+'\nsource_sha256='+sha+'\nstart='+start+'\n'); log.flush()
            cmd=['bash','evidence/preparation/lean-slot.sh','/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',mod]
            proc=subprocess.Popen(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
            (logdir/'current.pid').write_text(f'{proc.pid} {mod}\n')
            rc=proc.wait()
            end=datetime.datetime.now(datetime.timezone.utc).isoformat()
            log.write('end='+end+'\nrc='+str(rc)+'\n')
        output=path.read_text()
        a=len(re.findall(r'^\S+\.lean:\d+:\d+: error:',output,re.M))
        b=len(re.findall(r'^\S+\.lean:\d+:\d+: error\(',output,re.M))
        obj=tree/(mod+'.olean'); fresh=obj.is_file() and obj.stat().st_size>0
        summary.write(f'{mod}\t{head}\t{sha}\t{start}\t{end}\t{rc}\t{a}\t{b}\t{fresh}\n'); summary.flush()
        print('END',mod,'rc',rc,'errors',a,b,'olean',fresh,flush=True)
        if rc or a or b or not fresh:
            print(output[-10000:],flush=True)
            (logdir/'current.pid').unlink(missing_ok=True)
            failed.add(mod)
    (logdir/'current.pid').unlink(missing_ok=True)
print('DEVELOPMENT CHECKS',len(mods),'failed or skipped',len(failed),flush=True)
sys.exit(1 if failed else 0)
