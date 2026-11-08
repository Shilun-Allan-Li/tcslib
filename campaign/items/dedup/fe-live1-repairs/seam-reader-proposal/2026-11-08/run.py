from pathlib import Path
import subprocess,time,datetime,json,hashlib,sys
out=Path(__file__).resolve().parent
label,filename,overlayname,*options=sys.argv[1:]
project=out/'project';overlay=out/overlayname;native='native' in options
folder=out/'attempts'/label;folder.mkdir(exist_ok=False)
source=project/filename;data=source.read_bytes();(folder/'source.lean.txt').write_bytes(data)
helper=project/'devtools/seyoon'/('leanelab-o.sh' if native else 'leanelab.sh')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def objects():return {str(p.relative_to(overlay)):sha(p) for p in sorted(overlay.rglob('*.olean'))}
cmd=['bash',str(helper),str(project),str(overlay),filename]+([str(overlay)] if native else [])
record={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':'9936345ae64a4380bbec3ac6f3dad192f927420a','source_sha256':hashlib.sha256(data).hexdigest(),'command':cmd,'helper_sha256':sha(helper),'whole_MAC8_APFS_clone':True,'local_slots':3,'machine_cap':5,'own_Lean_jobs':1,'threads':4,'nice':10,'native':native}
if native:
 before=objects();(folder/'objects-before.json').write_text(json.dumps(before,indent=2)+'\n')
 for suffix in ['.olean','.ilean','.c','.trace']:(overlay/Path(filename).with_suffix(suffix)).unlink(missing_ok=True)
 record['input_object_count_before_unlink']=len(before);record['compiled_outputs_unlinked_before_run']=True
(folder/'request.json').write_text(json.dumps(record,indent=2)+'\n');start=time.monotonic()
with(folder/'raw.out').open('wb') as stream:r=subprocess.run(cmd,stdout=stream,stderr=subprocess.STDOUT)
raw=(folder/'raw.out').read_bytes();record.update({'exit':r.returncode,'seconds_including_wait':time.monotonic()-start,'raw_sha256':hashlib.sha256(raw).hexdigest(),'raw_bytes':len(raw),'errors':raw.count(b'error:'),'sorry_warnings':raw.count(b"declaration uses 'sorry'"),'source_unchanged_during_run':source.read_bytes()==data})
if native:
 after=objects();(folder/'objects-after.json').write_text(json.dumps(after,indent=2)+'\n');record.update({'output_object_count':len(after),'changed_existing_objects':[n for n in before if before[n]!=after.get(n)],'added_objects':[n for n in after if n not in before]})
(folder/'run.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
if r.returncode:
 lines=raw.decode().splitlines()
 for i,line in enumerate(lines):
  if 'error:' in line:print('\n'.join(lines[i:i+22]))
