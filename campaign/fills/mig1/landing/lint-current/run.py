from pathlib import Path
import os,subprocess,json,tempfile,hashlib,time,re
r=Path.cwd();o=r/'campaign/fills/mig1/landing/lint-current';wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad';temp=Path(tempfile.mkdtemp(prefix='tcslib-mig1-lint-',dir='/private/tmp'))
def git(*args):return subprocess.check_output(['git','-C',str(wt),*args])
def pin(ref):
 h=git('rev-parse',ref).decode().strip();subprocess.run(['git','-C',str(wt),'cat-file','-e',h+'^{commit}'],check=True);return h
refs={'base':pin('1160c18f'),'head':pin('HEAD')};files=git('diff','--name-only',refs['base'],refs['head'],'--','*.lean').decode().splitlines();assert len(files)==11
runs=[];inputs=[]
for stage,rev in refs.items():
 t=temp/stage;(t/'scripts').mkdir(parents=True)
 for script in ['campaign_style_lint.py','style_lint.py']:(t/'scripts'/script).write_bytes((r/'scripts'/script).read_bytes())
 for f in files:
  data=git('show',rev+':'+f);target=t/f;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);inert=o/'inputs'/stage/(f+'.txt');inert.parent.mkdir(parents=True,exist_ok=True);inert.write_bytes(data);inputs.append({'stage':stage,'revision':rev,'path':f,'sha256':hashlib.sha256(data).hexdigest()})
 for name,args in [('campaign',['TCSlib/Complexity']),('policy',files)]:
  script='campaign_style_lint.py' if name=='campaign' else 'style_lint.py';cmd=['python3','-I',str(t/'scripts'/script),*args];start=time.time();c=subprocess.run(cmd,cwd=t,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);out=o/(stage+'-'+name+'.out');out.write_bytes(c.stdout);runs.append({'stage':stage,'name':name,'command':cmd,'exit':c.returncode,'seconds':time.time()-start,'output_sha256':hashlib.sha256(c.stdout).hexdigest()})
(o/'runs.json').write_text(json.dumps({'refs':refs,'files':files,'scope':'same eleven owned Lean source files on both pinned trees, trusted scripts copied unchanged; inherited findings not silently waived','inputs':inputs,'runs':runs},indent=2)+'\n')
for row in runs:
 s=(o/(row['stage']+'-'+row['name']+'.out')).read_text();print(row['stage'],row['name'],'exit',row['exit'],'tail',s.splitlines()[-1])
