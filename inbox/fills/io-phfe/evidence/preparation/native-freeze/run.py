from pathlib import Path
import subprocess,os,json,sys,hashlib
root=Path.cwd();sysroot=Path('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0');env=dict(os.environ,LEAN_SLOT_TAG='io-phfe');env['LEAN_PATH']=':'.join(str(p) for p in [root/'.lake/io-phfe-audit-tools',root/'.lake/io-phfe-oleans',*sorted((root/'.lake/packages').glob('*/.lake/build/lib/lean'))]);tool=root/'evidence/preparation/native-freeze/NativeFreeze.lean';prefix=['bash',str(root/'evidence/preparation/lean-slot.sh'),str(sysroot/'bin/lean'),'--run',str(root/'evidence/preparation/native-freeze/RunNativeFreeze.lean')];tag=sys.argv[1];cmd=['python3','-I','evidence/preparation/native-freeze/native_freeze.py','--repo',str(root),'--original-manifest',str(root/'evidence/freeze/checkpoint0.json'),'--files-list',str(root/'evidence/logs/owned-files.txt'),'--parser-source',str(tool),'--parser-command-json',json.dumps(prefix),'--sysroot',str(sysroot),'--out',str(root/'evidence/freeze'/tag)];log=root/'evidence/freeze'/(tag+'-driver.log')
assert not log.exists()
compiled=json.loads((root/'evidence/freeze/native-tool-compile/result.json').read_text())
assert hashlib.sha256(tool.read_bytes()).hexdigest()==compiled['source_sha256']
assert hashlib.sha256((root/'.lake/io-phfe-audit-tools/NativeFreeze.olean').read_bytes()).hexdigest()==compiled['object_sha256']
assert hashlib.sha256((root/'evidence/preparation/native-freeze/RunNativeFreeze.lean').read_bytes()).hexdigest()==compiled['launcher_sha256']
(root/'evidence/freeze'/(tag+'-tool.json')).write_text(json.dumps(compiled,indent=2)+'\n')
with log.open('w') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
print('native freeze driver rc',r.returncode);print(log.read_text()[-7000:]);raise SystemExit(r.returncode)
