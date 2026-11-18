from pathlib import Path
import subprocess,os,json,hashlib
root=Path.cwd();tool=root/'evidence/preparation/native-freeze/NativeFreeze.lean';sysroot=Path('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0');env=dict(os.environ,LEAN_SLOT_TAG='io-phfe');env['LEAN_PATH']=':'.join(str(p) for p in [root/'.lake/io-phfe-oleans',*sorted((root/'.lake/packages').glob('*/.lake/build/lib/lean'))]);cmd=['bash','evidence/preparation/lean-slot.sh',str(sysroot/'bin/lean'),'--run',str(tool),str(sysroot),'TCSlib.Cryptography.Pairing.MatrixDH.Parameters','/private/tmp/io-phfe-native-freeze-smoke-request.json'];p=Path('evidence/freeze/native-smoke');p.mkdir(exist_ok=True);n=1
while (p/f'attempt{n}-source.lean.txt').exists():n+=1
(p/f'attempt{n}-source.lean.txt').write_bytes(tool.read_bytes());(p/f'attempt{n}-command.json').write_text(json.dumps({'argv':cmd,'source_sha256':hashlib.sha256(tool.read_bytes()).hexdigest()},indent=2)+'\n')
r=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(p/f'attempt{n}.log').write_text(r.stdout);print('attempt',n,'rc',r.returncode);print(r.stdout[:8500] if r.returncode else r.stdout[:500]);raise SystemExit(r.returncode)
