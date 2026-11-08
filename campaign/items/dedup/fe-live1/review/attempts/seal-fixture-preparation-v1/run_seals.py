from pathlib import Path
import os,subprocess,json,datetime,time,hashlib,re
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);project=O/'project';out=O/'sealed-runs';out.mkdir(exist_ok=True);rows=[]
files=[]
for d in json.loads((O/'SEAL-SOURCE-MAP.json').read_text()):
 files.append((project/('FE1Sealed_'+d['label']+'.lean'),'seal'))
 for side in ['native','sealed']:files.append((project/('FE1Controls_'+d['label']+'_'+side+'.lean'),'controls-'+side))
for f,kind in files:
 argv=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(project),str(S/'oleans-mac8'),str(f)];start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();r=subprocess.run(argv,cwd=project,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);raw=r.stdout;label=f.stem;(out/(label+'.out')).write_bytes(raw);d={'label':label,'kind':kind,'argv':argv,'start_utc':start,'seconds':time.monotonic()-t,'exit':r.returncode,'errors':len(re.findall(r': error(?:\([^\n]*?\))?:',raw.decode(errors='replace'))),'rfl_errors':raw.count(b'Tactic `rfl` failed'),'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'input_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(raw).hexdigest(),'output_bytes':len(raw),'one_own_Lean_at_a_time':True,'source':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','whole_snapshot':'oleans-mac8','source_only_draft':True};(out/(label+'-run.json')).write_text(json.dumps(d,indent=2)+'\n');rows.append(d);print(json.dumps(d),flush=True)
(O/'SEAL-RESULTS.json').write_text(json.dumps(rows,indent=2)+'\n')
