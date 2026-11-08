from pathlib import Path
import os,subprocess,json,hashlib,datetime,time,re,sys
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);out=O/'reader-runs';out.mkdir(exist_ok=True);rows=[]
labels=['ReaderControls'] if '--controls-only' in sys.argv[1:] else ['ActionReader','ReaderControls']
for label in labels:
 for side in ['native','sealed']:
  f=O/'project'/('FE1'+label+'_'+side+'.lean');argv=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(O/'project'),str(S/'oleans-mac8'),str(f)];t=time.monotonic();start=datetime.datetime.now(datetime.timezone.utc).isoformat();r=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);b=r.stdout;(out/(f.stem+'.out')).write_bytes(b);d={'label':f.stem,'argv':argv,'start_utc':start,'seconds':time.monotonic()-t,'exit':r.returncode,'errors':len(re.findall(r': error(?:\([^\n]*?\))?:',b.decode(errors='replace'))),'input_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(b).hexdigest(),'output_bytes':len(b),'source':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','whole_snapshot':'oleans-mac8','one_own_Lean_at_a_time':True};(out/(f.stem+'-run.json')).write_text(json.dumps(d,indent=2)+'\n');rows.append(d);print(json.dumps(d),flush=True)
(O/'READER-RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n')
