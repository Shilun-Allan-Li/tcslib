from pathlib import Path
import datetime, hashlib, json, os, platform, re, shutil, subprocess, sys
r=Path.cwd()
out=Path(__file__).resolve().parent
logs=out/"logs"; logs.mkdir(parents=True,exist_ok=True)
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
vm=subprocess.check_output(["vm_stat"],text=True)
page=int(re.search(r"page size of (\d+) bytes",vm).group(1))
fields={m.group(1):int(m.group(2)) for m in re.finditer(r"^(Pages (?:free|inactive|speculative)):\s+(\d+)",vm,re.M)}
headroom=sum(fields.values())*page
pre={"utc":now(),"platform":platform.platform(),"cpu_count":os.cpu_count(),"physical_memory_bytes":int(subprocess.check_output(["sysctl","-n","hw.memsize"],text=True)),"macos_headroom_proxy_bytes":headroom,"proxy_formula":"(free + inactive + speculative vm_stat pages) * native page size; not Linux MemAvailable/cgroup accounting","clone_disk_free_bytes":shutil.disk_usage(r).free,"object_tree_disk_free_bytes":shutil.disk_usage(Path.home()/"phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4").free,"worktree":str(r)}
(logs/"preflight.log").write_text(json.dumps(pre,indent=2)+"\n\n"+vm+"\n"+subprocess.check_output(["df","-k",str(r),str(out)],text=True))
assert headroom>=4*1024**3,"E-RES: native memory proxy below 4 GiB"
assert pre["clone_disk_free_bytes"]>=12*1024**3,"E-RES: disk below 12 GiB"
manifest=json.loads((r/"lake-manifest.json").read_text())
packages=r/".lake/packages"; lines=["PACKAGE_TREE "+str(packages.resolve())]; present=0; absent=[]
for pkg in manifest["packages"]:
    pp=packages/pkg["name"]
    if not pp.exists():absent.append(pkg["name"]); lines.append("ABSENT "+pkg["name"]);continue
    url=subprocess.check_output(["git","-C",str(pp),"remote","get-url","origin"],text=True).strip()
    rev=subprocess.check_output(["git","-C",str(pp),"rev-parse","HEAD"],text=True).strip()
    assert url==pkg["url"],("package URL mismatch",pkg["name"],url,pkg["url"])
    assert rev==pkg["rev"],("package revision mismatch",pkg["name"],rev,pkg["rev"])
    present+=1; lines.append("MATCH "+pkg["name"]+" "+url+" "+rev)
lines.append("PASS: every present package matches manifest; absent="+",".join(absent))
(logs/"packages.log").write_text("\n".join(lines)+"\n")
store=Path(os.environ.get("MATHLIB_CACHE_DIR",str(Path(os.environ.get("XDG_CACHE_HOME",str(Path.home()/".cache")))/"mathlib")))
archives=[x for x in store.rglob("*") if x.is_file()] if store.exists() else []
(logs/"cache-store.log").write_text(json.dumps({"path":str(store),"exists":store.exists(),"files":len(archives),"bytes":sum(x.stat().st_size for x in archives),"origin":"existing cache tool archive store; previous same-chat narrowed fetches, not downloaded by this step"},indent=2)+"\n")
roots=(r/".lake/ps-maintainer/gate06/roots-current.txt").read_text().splitlines(); assert len(roots)==145
assert all(re.fullmatch(r"Mathlib\.[A-Za-z0-9_.]+",x) for x in roots)
(out/"mathlib-roots.txt").write_text("\n".join(roots)+"\n")
env=os.environ.copy(); env["PATH"]=str(Path.home()/".elan/bin")+os.pathsep+env["PATH"]; env["TAR_OPTIONS"]="--no-same-owner"
cmd=["/usr/bin/time","-l","lake","exe","cache","get",*roots]
with (logs/"cache-get.log").open("w") as f:
    f.write("START "+now()+"\nCOMMAND "+json.dumps(cmd)+"\n");f.flush()
    proc=subprocess.Popen(cmd,stdout=f,stderr=subprocess.STDOUT,env=env)
    (logs/"cache.pid").write_text(str(proc.pid)+"\n")
    rc=proc.wait(); f.write("\nEND "+now()+" RC "+str(rc)+"\n")
assert rc==0,"narrowed cache failed; see cache-get.log"
zero=[str(x) for x in packages.resolve().rglob("*.olean") if x.stat().st_size==0]
(logs/"zero-oleans.log").write_text("\n".join(zero)+("\n" if zero else "")); assert not zero
probe=r/".lake/ps-maintainer/gate06/CacheProbe.lean"; probe.write_text("import "+roots[0]+"\n")
ol=Path.home()/"phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/oleans-gate06-r1"; ol.mkdir(parents=True,exist_ok=True); env["TCSLIB_OLEANS"]=str(ol)
with (logs/"cache-probe.log").open("w") as f:
    proc=subprocess.Popen(["/usr/bin/time","-l","bash","scripts/lean_check_tree.sh",".lake/ps-maintainer/gate06/CacheProbe"],stdout=f,stderr=subprocess.STDOUT,env=env)
    (logs/"probe.pid").write_text(str(proc.pid)+"\n"); rc=proc.wait()
assert rc==0,"cache probe failed"
(out/"setup-summary.json").write_text(json.dumps({"utc":now(),"roots":len(roots),"cache_rc":0,"cache_probe_rc":0,"olean_tree":str(ol),"present_packages":present,"absent_packages":absent},indent=2)+"\n")
print("PASS: native preflight, package pins, 145-root narrowed cache, zero-object scan and cache probe",flush=True)
