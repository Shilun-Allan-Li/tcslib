from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys, time
r=Path.cwd(); out=Path(__file__).resolve().parent
start=int(sys.argv[1]) if len(sys.argv)>1 else 1
label=sys.argv[2] if len(sys.argv)>2 else "pass1"
order_path=Path(sys.argv[3]) if len(sys.argv)>3 else r/".lake/ps-maintainer/gate06/order-current.txt"
order=order_path.read_text().splitlines()
logs=out/"logs"/label; logs.mkdir(parents=True,exist_ok=True)
assert not (logs/"replay.jsonl").exists(),"Do not overwrite a previous attempt"
(out/(label+"-order.txt")).write_text("\n".join(order)+"\n")
env=os.environ.copy(); env["PATH"]=str(Path.home()/".elan/bin")+os.pathsep+env["PATH"]
env["TCSLIB_OLEANS"]=json.loads((out/"setup-summary.json").read_text())["olean_tree"]
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
with (logs/"replay.jsonl").open("w") as summary:
    for index,module in enumerate(order,1):
        if index<start:continue
        path=r/(module+".lean"); sha=hashlib.sha256(path.read_bytes()).hexdigest()
        log=logs/"modules"/(module+".log"); log.parent.mkdir(parents=True,exist_ok=True)
        begun=now(); tick=time.monotonic()
        with log.open("w") as f:
            f.write("START "+begun+"\nSOURCE_SHA256 "+sha+"\n");f.flush()
            proc=subprocess.Popen(["/usr/bin/time","-l","bash","scripts/lean_check_tree.sh",module],stdout=f,stderr=subprocess.STDOUT,env=env)
            (logs/"current.pid").write_text(str(proc.pid)+"\n")
            rc=proc.wait(); end=now(); elapsed=time.monotonic()-tick; f.write("\nEND "+end+" RC "+str(rc)+"\n")
        obj=Path(env["TCSLIB_OLEANS"])/(module+".olean")
        same=hashlib.sha256(path.read_bytes()).hexdigest()==sha
        rss=re.search(r"(\d+)\s+maximum resident set size",log.read_text())
        item={"index":index,"total":len(order),"module":module,"rc":rc,"start":begun,"end":end,"elapsed_seconds":round(elapsed,3),"peak_rss_bytes":int(rss.group(1)) if rss else None,"source_sha256":sha,"source_unchanged_during_check":same,"fresh_nonempty_object":rc==0 and obj.is_file() and obj.stat().st_size>0,"object_sha256":hashlib.sha256(obj.read_bytes()).hexdigest() if rc==0 and obj.is_file() else None}
        summary.write(json.dumps(item)+"\n");summary.flush()
        print(str(index)+"/"+str(len(order))+" "+module+" rc="+str(rc)+" seconds="+str(item["elapsed_seconds"]),flush=True)
        if rc or not same or not item["fresh_nonempty_object"]:
            print("STOP: do not check dependent modules before repairing this failure",flush=True);sys.exit(rc or 1)
print("DONE "+now(),flush=True)
