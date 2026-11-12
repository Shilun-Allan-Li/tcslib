import sys,os,json,hashlib,subprocess,time,datetime,shutil
from pathlib import Path
wt=Path(sys.argv[1]).resolve();branch=sys.argv[2];name=sys.argv[3];targets=sys.argv[4:]
s=Path(os.environ['TCSLIB_SCRATCH']);ev=Path('/private/tmp')/('ab34-'+name+'-replay');ev.mkdir()
cfg=json.loads(Path(sys.argv[0]).with_name(name+'-chain-plan.json').read_text());inp=s/cfg['input_snapshot'];out=s/('oleans-'+name)
def sh(args,**kw):return subprocess.check_output(args,**kw).decode().strip()
def git(*args):return sh(['git','-C',str(wt),*args])
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,v):(ev/n).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def objects(p):return {str(f.relative_to(p)):sha(f.read_bytes()) for f in sorted(p.rglob('*.olean'))}
def leanmap():
 return {p:{'git_blob':git('rev-parse','HEAD:'+p),'sha256':sha((wt/p).read_bytes()),'bytes':(wt/p).stat().st_size} for p in git('ls-files','*.lean').splitlines()}
head=git('rev-parse','HEAD');base=git('rev-parse',cfg['input_source']);records=git('rev-parse','origin/complexity/arora-barak-ch3-4')
for rev in [head,base,records]:subprocess.run(['git','-C',str(wt),'cat-file','-e',rev+'^{commit}'],check=True)
assert head==cfg['head']==git('rev-parse',branch)
for source_branch,pin in cfg['heads'].items():assert pin==git('rev-parse','origin/'+source_branch)
assert not git('status','--porcelain','--untracked-files=no')
assert not git('diff','--name-only',cfg['campaign_Lean'],records,'--','*.lean')
records_is_ancestor=git('merge-base',records,head)==records
if records_is_ancestor:
 prospective_tree=git('rev-parse','HEAD^{tree}')
else:
 prospective=subprocess.run(['git','-C',str(wt),'merge-tree','--write-tree',records,head],capture_output=True,text=True)
 assert prospective.returncode==0,prospective.stdout+prospective.stderr
 prospective_tree=prospective.stdout.splitlines()[0]
 subprocess.run(['git','-C',str(wt),'cat-file','-e',prospective_tree+'^{tree}'],check=True)
 assert not git('diff','--name-only',head,prospective_tree,'--','*.lean')
assert not out.exists() and inp.is_dir()
assert (wt/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib').is_dir()
changes=git('diff','--name-only',base,head,'--','*.lean').splitlines()
assert sorted(targets)==sorted(p[:-5].replace('/','.') for p in changes)
for n in ['leanelab-o.sh','mkdownmulti.py','graph.py']:
 b=(wt/'devtools/seyoon'/n).read_bytes();(ev/n).write_bytes(b)
shutil.copyfile(__file__,ev/'driver.py')
subprocess.run(['python3','-I',str(wt/'devtools/seyoon/mkdownmulti.py'),str(wt),str(wt/'devtools/seyoon'),str(ev/'down.txt'),*targets],check=True)
mods=(ev/'down.txt').read_text().splitlines();assert 'TCSlib' not in mods
source=leanmap();write('source-before.json',source)
for p in changes:
 d=ev/'source'/str(p+'.txt');d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes((wt/p).read_bytes())
original=objects(inp);assert len(original)==cfg['expected_input_objects']
assert original==json.loads(Path(cfg['input_map']).read_text())
previous_result=json.loads((Path(cfg['input_evidence'])/'RESULT.json').read_text());assert previous_result['pass'] and previous_result['head']==base
write('chain-plan.json',cfg);shutil.copyfile(cfg['input_map'],ev/'previous-output-map.json');shutil.copyfile(Path(cfg['input_evidence'])/'RESULT.json',ev/'previous-RESULT.json');shutil.copyfile(s/'api/staticsorry.py',ev/'staticsorry.py')

write('input-before.json',original)
write('request.json',{'head':head,'records':records,'snapshot_lean_commit':base,'snapshot':str(inp),'output':str(out),'branch':branch,'targets':targets,'changed_files':changes,'modules':len(mods),'local_slots':os.environ.get('TCSLIB_LEAN_SLOTS'),'machine_cap':5,'whole_clone':'cp -cR','prospective_tree':prospective_tree,'records_is_ancestor':records_is_ancestor,'prospective_Lean_equals_pushed_head':True,'records_change_no_Lean_from_MAC8':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
subprocess.run(['cp','-cR',str(inp),str(out)],check=True)
assert objects(out)==original
rows=[];start=time.monotonic()
with (ev/'replay.log').open('w') as log:
 log.write('# '+name+' head '+head+'; complete passed snapshot clone; all module output in logs/\n');log.flush()
 for i,m in enumerate(mods):
  f=m+'.lean';op=out/(m+'.olean')
  for ext in ['.olean','.ilean','.c','.trace']:(out/(m+ext)).unlink(missing_ok=True)
  assert not op.exists()
  lp=ev/'logs'/(m+'.log');lp.parent.mkdir(parents=True,exist_ok=True)
  t=time.monotonic()
  with lp.open('wb') as lf:
   r=subprocess.run(['bash',str(wt/'devtools/seyoon/leanelab-o.sh'),str(wt),str(out),f,str(out)],stdout=lf,stderr=subprocess.STDOUT)
  raw=lp.read_bytes();errors=raw.count(b'error:');sorries=raw.count(b"declaration uses 'sorry'")
  ok=r.returncode==0 and errors==0 and op.is_file() and op.stat().st_size>0
  row={'module':m,'exit':r.returncode,'errors':errors,'sorry':sorries,'seconds':time.monotonic()-t,'fresh_output':op.is_file(),'log_sha256':sha(raw),'pass':ok}
  rows.append(row);line=f'{m} exit={r.returncode} errors={errors} sorry={sorries}'
  log.write(line+'\n');log.flush();write('progress.json',{'completed':len(rows),'modules':len(mods),'last':row})
  print(f'{name} {i+1}/{len(mods)} {m} '+('PASS' if ok else 'FAIL'),flush=True)
  if not ok:break
 log.write(f'# modules={len(rows)} failed={sum(not r["pass"] for r in rows)}\n')
write('module-results.json',rows)
write('input-after.json',objects(inp));assert objects(inp)==original
new=objects(out);write('output.json',new)
added=set()
for source_path in changes:
 if subprocess.run(['git','-C',str(wt),'cat-file','-e',base+':'+source_path],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0:added.add(source_path[:-5]+'.olean')
assert set(new)==set(original)|added and len(new)==cfg['expected_output_objects']
write('new-module-accounting.json',{'new_oleans':sorted(added),'input_objects':len(original),'output_objects':len(new)})

changed=[p for p in new if new[p]!=original.get(p)];allowed={m+'.olean' for m in mods};assert set(changed)<=allowed
write('object-accounting.json',{'input_objects':len(original),'output_objects':len(new),'input_unchanged':True,'changed_objects':changed,'changed_count':len(changed),'outside_closure_unchanged':True})
assert leanmap()==source and git('rev-parse','HEAD')==head
st=subprocess.run(['python3','-I',str(s/'api/staticsorry.py'),str(wt),str(ev/'replay.log')],capture_output=True)
(ev/'static.txt').write_bytes(st.stdout+st.stderr)
import re
static_match=re.search(r'modules (\d+), mismatches (\d+), static total (\d+)',st.stdout.decode())
static_pass=st.returncode==0 and static_match is not None and int(static_match.group(1))==len(mods) and int(static_match.group(2))==0 and (cfg['expected_static'] is None or int(static_match.group(3))==cfg['expected_static'])
write('static-comparison.json',{'exit':st.returncode,'parsed':static_match.groups() if static_match else None,'pass':static_pass,'helper_sha256':sha((ev/'staticsorry.py').read_bytes())})
passed=len(rows)==len(mods) and all(r['pass'] for r in rows) and static_pass

write('RESULT.json',{'pass':passed,'head':head,'modules':len(rows),'expected_modules':len(mods),'failed':sum(not r['pass'] for r in rows),'static_exit':st.returncode,'seconds':time.monotonic()-start,'snapshot_valid':passed,'complete_input_objects':len(original),'complete_output_objects':len(new),'source_unchanged_during_replay':True})
print('REPLAY FINAL',name,'PASS' if passed else 'FAIL',flush=True)
if not passed:sys.exit(1)
