from pathlib import Path
import json,subprocess,os,hashlib,datetime,time,shutil,sys
O=Path(__file__).parent;C=json.loads((O/'CONTEXT.json').read_text());W=Path(C['private_source_tree']);OV=Path(C['private_complete_clone']);H=lambda b:hashlib.sha256(b).hexdigest();(O/'runs').mkdir(exist_ok=True)
def run(label,file,compile=False):
 d=O/'runs'/label;d.mkdir();p=W/file;assert p.is_file();(d/'source.lean.txt').write_bytes(p.read_bytes());script=C['approved_helper_paths']['leanelab-o.sh' if compile else 'leanelab.sh'];assert H(Path(script).read_bytes())==C['approved_helper_SHA256'][Path(script).name]
 args=['bash',script,str(W),str(OV),file]+([str(OV)] if compile else [])
 if compile:
  stem=OV/str(Path(file).with_suffix(''))
  for ext in ['.olean','.ilean','.c','.trace']:
   q=Path(str(stem)+ext)
   if q.exists():q.unlink()
 request={'label':label,'argv':args,'source_SHA256':H(p.read_bytes()),'source_path':str(p),'TCSLIB_SCRATCH':os.environ['TCSLIB_SCRATCH'],'TCSLIB_LEAN_SLOTS':os.environ.get('TCSLIB_LEAN_SLOTS'),'single_sequential_Lean_process_by_driver':True,'started_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat()};(d/'request.json').write_text(json.dumps(request,indent=2)+'\n');print('START',label,flush=True);start=time.monotonic()
 with (d/'raw.out').open('wb') as f:r=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT)
 rec=request|{'actual_exit':r.returncode,'elapsed_seconds':time.monotonic()-start,'finished_UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'raw_out_SHA256':H((d/'raw.out').read_bytes())};(d/'run.json').write_text(json.dumps(rec,indent=2)+'\n');print('DONE',label,'exit',r.returncode,'seconds',round(rec['elapsed_seconds'],2),flush=True)
 if r.returncode:print((d/'raw.out').read_text(),flush=True);sys.exit(r.returncode)
def probe(tag):
 name=tag+'.lean';(W/name).write_bytes((O/'probes'/(tag+'.lean.txt')).read_bytes());run(tag,name)
# Resolve the observed automatic universe-parameter renaming in the same complete clone.
# Candidate objects are saved byte-for-byte; original input objects are only read.
backup=Path(C['runtime'])/'candidate-object-backup';backup.mkdir()
paths=['TCSlib/Complexity/TuringMachine/Configuration.lean','TCSlib/Complexity/TuringMachine/Simulation.lean']
phase=[]
for path in paths:
 rel=str(Path(path).with_suffix('.olean'));obj=OV/rel;save=backup/Path(rel).name;save.write_bytes(obj.read_bytes());phase.append({'path':rel,'candidate_saved_SHA256':H(save.read_bytes())})
 (W/path).write_bytes((O/'source'/'BASE'/(path+'.txt')).read_bytes())
# Restore the exact input Configuration object; compile current0f Simulation against that unchanged owner context.
rel=str(Path(paths[0]).with_suffix('.olean'));(OV/rel).unlink();shutil.copyfile(Path(C['whole_input_snapshot'])/rel,OV/rel)
run('08-BASE-Simulation-normalization-context','TCSlib/Complexity/TuringMachine/Simulation.lean',True)
probe('BASE-normalized-metadata')
for path in paths:
 rel=str(Path(path).with_suffix('.olean'));obj=OV/rel;save=backup/Path(rel).name;obj.unlink();shutil.copyfile(save,obj);assert H(obj.read_bytes())==H(save.read_bytes());(W/path).write_bytes((O/'source'/'CANDIDATE'/(path+'.txt')).read_bytes())
(O/'NORMALIZATION-PHASE-RESTORATION.json').write_text(json.dumps({'phase_objects':phase,'candidate_objects_restored_byte_exact':True,'input_snapshot_written':False,'same_complete_895_object_clone':True},indent=2)+'\n')
probe('CANDIDATE-normalized-metadata')
print('COMPLETE universe-normalization comparison',flush=True)
