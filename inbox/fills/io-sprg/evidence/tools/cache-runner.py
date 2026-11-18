# io-sprg: foreground narrowed cache runner; original tool for this task.
import datetime, os, pathlib, subprocess, sys
root=pathlib.Path.cwd()
roots=(root/'evidence/logs/mathlib-roots.txt').read_text().splitlines()
assert roots and all(x.startswith('Mathlib.') and x.replace('.','').isalnum() for x in roots)
env=dict(os.environ)
env['LEAN_SLOT_TAG']='io-sprg'
env['PATH']=str(pathlib.Path.home()/'.elan/bin')+':'+env['PATH']
cmd=['/private/tmp/io-sprg-tools/lean-slot.sh','-k','3','/usr/bin/time','-l',
     'env','TAR_OPTIONS=--no-same-owner','lake','exe','cache','get',*roots]
log=root/(sys.argv[1] if len(sys.argv)>1 else 'evidence/logs/cache-get.log')
with log.open('w') as out:
    out.write(datetime.datetime.now(datetime.timezone.utc).isoformat()+' START\n')
    out.flush()
    proc=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT,env=env)
    (root/'evidence/logs/cache-wrapper.pid').write_text(str(proc.pid)+'\n')
    rc=proc.wait()
    out.write(datetime.datetime.now(datetime.timezone.utc).isoformat()+f' END rc={rc}\n')
print(f'cache rc={rc}; log={log}',flush=True)
sys.exit(rc)
