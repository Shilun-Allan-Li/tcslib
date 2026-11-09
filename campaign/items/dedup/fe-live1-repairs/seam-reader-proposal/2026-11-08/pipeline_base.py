from pathlib import Path
import subprocess,json,sys
out=Path(__file__).resolve().parent
for args in json.loads(Path(sys.argv[1]).read_text()):
 subprocess.run([sys.executable,'-I',str(out/'run_base.py'),*args],check=True)
 record=json.loads((out/'attempts'/args[0]/'run.json').read_text())
 if (record['exit']!=0) != ('expect-fail' in args):raise SystemExit(1)
