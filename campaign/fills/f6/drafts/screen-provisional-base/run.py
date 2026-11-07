from pathlib import Path
import hashlib,json,subprocess,datetime,time,os
R=Path(__file__).resolve().parents[5]
S=Path(os.environ["TCSLIB_SCRATCH"])
O=Path(__file__).resolve().parent
W=S/"wt-natbits"
rev=subprocess.check_output(["git","-C",str(W),"rev-parse","HEAD"],text=True).strip()
subprocess.run(["git","-C",str(W),"cat-file","-e",rev+"^{commit}"],check=True)
assert rev=="1160c18f03fd318f0dec25738790935fa61379d4"
pop=R/"campaign/fills/f6/drafts/final-brief-review/provisional-TCSlib-screen.txt"
paths=[x for x in pop.read_text().splitlines() if x.strip()]
assert len(paths)==21 and len(set(paths))==21 and all(x.startswith("TCSlib/") and x.endswith(".lean") for x in paths)
stage=S/"stage/f6-provisional-screen-base"
assert not stage.exists()
stage.mkdir(parents=True)
source=[]
for p in paths:
 b=subprocess.check_output(["git","-C",str(W),"show",rev+":"+p]);q=stage/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 z=O/"inputs"/(p+".txt");z.parent.mkdir(parents=True,exist_ok=True);z.write_bytes(b)
 source.append({"path":p,"sha256":hashlib.sha256(b).hexdigest(),"bytes":len(b),"git_blob":subprocess.check_output(["git","-C",str(W),"rev-parse",rev+":"+p],text=True).strip()})
tool=R/"scripts/copy-text-screen-v3.py"
assert tool.read_bytes()==subprocess.check_output(["git","-C",str(W),"show",rev+":scripts/copy-text-screen-v3.py"])
(O/"copy-text-screen-v3.py.txt").write_bytes(tool.read_bytes())
cmd=["nice","-n","10","python3","-I",str(tool),str(stage),*paths]
start={"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"status":"running; no pass claimed","source":rev,"files":source,"population_sha256":hashlib.sha256(pop.read_bytes()).hexdigest(),"tool_sha256":hashlib.sha256(tool.read_bytes()).hexdigest(),"command":cmd,"scope":"Provisional unissued21-file TCSlib baseline; active19 plus actual UniversalK citation and conservative Universal comparison. Named Mathlib sources assessed separately, not silently counted as TCSlib."}
(O/"start.json").write_text(json.dumps(start,indent=2)+"\n")
lock=S/"locks/screen"
lock.parent.mkdir(parents=True,exist_ok=True)
try:lock.mkdir()
except FileExistsError:raise SystemExit("screen lock occupied; no screen run")
try:
 t=time.monotonic()
 with (O/"screen.out").open("w") as f:res=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 receipt={**start,"completed_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"seconds":time.monotonic()-t,"exit":res.returncode,"output_sha256":hashlib.sha256((O/"screen.out").read_bytes()).hexdigest(),"status":"PASS" if res.returncode==0 else "FAIL"}
 for a in source:assert hashlib.sha256((stage/a["path"]).read_bytes()).hexdigest()==a["sha256"]
 (O/"run.json").write_text(json.dumps(receipt,indent=2)+"\n")
 print(json.dumps({k:receipt[k] for k in ["status","source","exit","seconds","output_sha256"]}),flush=True)
 raise SystemExit(res.returncode)
finally:lock.rmdir()
