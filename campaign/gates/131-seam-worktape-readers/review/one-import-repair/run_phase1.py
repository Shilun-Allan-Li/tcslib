from pathlib import Path
import json,subprocess,os,hashlib,datetime,time,shutil,sys
O=Path(__file__).parent;C=json.loads((O/'CONTEXT.json').read_text());W=Path(C['private_source_tree']);OV=Path(C['private_complete_clone']);H=lambda b:hashlib.sha256(b).hexdigest();(O/'runs').mkdir(exist_ok=True)
def run(label,file,compile=False,expected_exit=0):
 d=O/'runs'/label;d.mkdir();p=W/file;assert p.is_file();(d/'source.lean.txt').write_bytes(p.read_bytes());script=C['approved_helper_paths']['leanelab-o.sh' if compile else 'leanelab.sh'];assert H(Path(script).read_bytes())==C['approved_helper_SHA256'][Path(script).name]
 args=['bash',script,str(W),str(OV),file]+([str(OV)] if compile else [])
 if compile:
  stem=OV/str(Path(file).with_suffix(''))
  for ext in ['.olean','.ilean','.c','.trace']:
   q=Path(str(stem)+ext)
   if q.exists():q.unlink()
 request={'label':label,'expected_exit':expected_exit,'argv':args,'source_SHA256':H(p.read_bytes()),'source_path':str(p),'TCSLIB_SCRATCH':os.environ['TCSLIB_SCRATCH'],'TCSLIB_LEAN_SLOTS':os.environ.get('TCSLIB_LEAN_SLOTS'),'single_sequential_Lean_process_by_driver':True,'started_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat()};(d/'request.json').write_text(json.dumps(request,indent=2)+'\n');print('START',label,flush=True);start=time.monotonic()
 with (d/'raw.out').open('wb') as f:r=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT)
 rec=request|{'actual_exit':r.returncode,'elapsed_seconds':time.monotonic()-start,'finished_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'raw_out_SHA256':H((d/'raw.out').read_bytes())};(d/'run.json').write_text(json.dumps(rec,indent=2)+'\n');print('DONE',label,'exit',r.returncode,'seconds',round(rec['elapsed_seconds'],2),flush=True)
 if r.returncode!=expected_exit:print((d/'raw.out').read_text(),flush=True);sys.exit(r.returncode)
def probe(tag):
 name=tag+'.lean';(W/name).write_bytes((O/'probes'/(tag+'.lean.txt')).read_bytes());run(tag,name)
# BASE metadata uses the complete cloned actual131 object context.
name='00-no-import-gap.lean';(W/name).write_bytes((O/'probes/00-no-import-gap.lean.txt').read_bytes());run('00-no-import-gap',name,False,1)
probe('01-BASE-target-metadata')
path='TCSlib/Complexity/TuringMachine/Build/Seam.lean'
(W/path).write_bytes((O/'Seam-CANDIDATE.lean.txt').read_bytes())
try:
  run('02-CANDIDATE-full-owner-native',path,True)
  probe('03-CANDIDATE-target-metadata')
finally:
  (W/path).write_bytes((O/'Seam-BASE.lean.txt').read_bytes())
print('COMPLETE one-import repair native and metadata',flush=True)
