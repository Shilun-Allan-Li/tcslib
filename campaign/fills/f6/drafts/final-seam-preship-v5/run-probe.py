from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,sys,tempfile,time
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
name=sys.argv[1];src=OUT/(name+'.lean.txt');log=OUT/(name+'.out');receipt=OUT/(name+'-run.json')
assert not log.exists() and not receipt.exists()
data=src.read_bytes();tmp=Path(tempfile.mkdtemp(prefix='tcslib-f6-final-seam-',dir='/private/tmp'));file=tmp/(name.replace('-','_')+'.lean');file.write_bytes(data)
wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-natbits');ol=wt.parent/'oleans-mra2'
assert (ol/'TCSlib/Complexity/SpaceComplexity/Hierarchy.olean').is_file()
command=['bash',str(ROOT/'devtools/seyoon/leanelab.sh'),str(wt),str(ol),str(file)]
start=time.time();row={'command':command,'input_sha256':hashlib.sha256(data).hexdigest(),'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'local_slots':os.environ.get('TCSLIB_LEAN_SLOTS'),'plain_managed':True,'no_outer_lock':True}
(OUT/(name+'-request.json')).write_text(json.dumps(row,indent=2)+'\n')
r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(r.stdout);text=r.stdout.decode(errors='replace')
row.update(exit=r.returncode,seconds=time.time()-start,errors=len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',text,re.M)),output_sha256=hashlib.sha256(r.stdout).hexdigest())
receipt.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row,indent=2));print(text)
