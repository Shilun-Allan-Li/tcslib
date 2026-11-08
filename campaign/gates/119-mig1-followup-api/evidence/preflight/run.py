from pathlib import Path
import os,subprocess,hashlib,json,time,datetime
R=Path("/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4")
W=Path("/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4")
S=Path(os.environ["TCSLIB_SCRATCH"]);O=Path(__file__).parent
source=S/"oleans-mra2";tree=S/"oleans-mfollowup-preflight"
assert source.is_dir() and not tree.exists()
subprocess.run(["cp","-cR",str(source),str(tree)],check=True)
files=["TCSlib/Complexity/TuringMachine/Finite.lean","TCSlib/Complexity/TuringMachine/Encoding.lean","TCSlib/Complexity/TuringMachine/Build/Wrappers.lean","TCSlib/Complexity/TuringMachine/Build/Primitives.lean","TCSlib/Complexity/TuringMachine/Build/Catalog.lean"]
setup={"start_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"parent_complete_tree":str(source),"complete_output_tree":str(tree),"order":files,"scope":"Five actual changed modules in one full mra2 copy; not a full downstream replay"}
(O/"setup.json").write_text(json.dumps(setup,indent=2)+"\n");runs=[]
for f in files:
 b=(W/f).read_bytes();name=Path(f).stem;(O/(name+".lean.txt")).write_bytes(b)
 base=tree/f.removesuffix(".lean")
 for ext in [".olean",".ilean",".c",".trace"]:base.with_suffix(ext).unlink(missing_ok=True)
 cmd=["bash",str(R/"devtools/seyoon/leanelab-o.sh"),str(W),str(tree),f,str(tree)]
 t=time.monotonic();res=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);raw=res.stdout;(O/(name+".out")).write_bytes(raw)
 d={"source":f,"source_sha256":hashlib.sha256(b).hexdigest(),"command":cmd,"seconds":time.monotonic()-t,"exit":res.returncode,"errors":raw.count(b"error:"),"warnings":raw.count(b"warning:"),"sorry_warnings":raw.count(b"declaration uses 'sorry'"),"output_sha256":hashlib.sha256(raw).hexdigest(),"source_stable":b==(W/f).read_bytes()}
 (O/(name+"-run.json")).write_text(json.dumps(d,indent=2)+"\n");runs.append(d);print(json.dumps({k:d[k] for k in ["source","exit","errors","sorry_warnings","seconds"]}),flush=True)
 assert d["exit"]==0 and d["errors"]==0 and d["source_stable"],d
 assert base.with_suffix(".olean").is_file()
for f in files:
 expected=(O/(Path(f).stem+".lean.txt")).read_bytes();assert expected==(W/f).read_bytes()
(O/"receipt.json").write_text(json.dumps({**setup,"completed_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"modules":len(runs),"failures":0,"runs":runs},indent=2)+"\n")
