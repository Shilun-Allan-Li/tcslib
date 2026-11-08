from pathlib import Path
import base64,datetime,hashlib,io,json,os,subprocess,tarfile
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
C=json.loads((OUT/'capture.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def git(*args,wt=ROOT):return subprocess.run(['git','-C',str(wt),*args],check=True,stdout=subprocess.PIPE).stdout
def read(p):return json.loads(p.read_text())
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
assert len(C['population'])==len(set(C['population']))==25
assert (OUT/'population.txt').read_text().splitlines()==C['population']
assert (ROOT/C['population_source']).read_bytes()==(OUT/'population.txt').read_bytes()
for label in ['base','head','previous_base','previous_head','merged_API']:
 pin=C[label];assert git('rev-parse',pin).decode().strip()==pin;git('cat-file','-e',pin+'^{commit}')
assert git('diff',C['merged_API'],C['base'],'--','*.lean')==b''
selected=[];side_runs={}
for side in ['base','head']:
 archive=base64.b64decode((OUT/(side+'.tar.base64.txt')).read_bytes(),validate=False)
 assert sha(archive)==C['sides'][side]['archive_sha256'] and len(archive)==C['sides'][side]['archive_bytes']
 with tarfile.open(fileobj=io.BytesIO(archive),mode='r:') as tf:
  members={m.name:m for m in tf.getmembers() if m.isfile()};assert set(members)==set(C['population'])
  sc=read(OUT/(side+'-capture.json'));assert sc['side']==side and sc['commit']==C[side] and sc['population']==C['population']
  assert sc['files']==C['sides'][side]['files'] and sc['archive_sha256']==sha(archive)
  for row in C['sides'][side]['files']:
   path=row['path'];data=git('show',C[side]+':'+path);blob=git('rev-parse',C[side]+':'+path).decode().strip()
   assert blob==row['blob'] and sha(data)==row['sha256'] and len(data)==row['bytes']
   assert tf.extractfile(members[path]).read()==data
   assert (OUT/'inputs'/side/(path+'.txt')).read_bytes()==data
   assert (Path(C['temporary_trees'][side])/path).read_bytes()==data
   assert data.decode('utf-8').encode('utf-8')==data
   selected.append(dict(side=side,commit=C[side],path=path,blob=blob,bytes=len(data),sha256=sha(data),Git_archive_inert_plaintext_private_export_equal=True))
 r=read(OUT/(side+'-run.json'));request=read(OUT/(side+'-request.json'));assert r['exit']==0 and r['fresh_execution'] and r['full_population']==25 and r['source_commit']==C[side]
 assert r['side_capture_sha256']==sha((OUT/(side+'-capture.json')).read_bytes()) and r['orchestrator_sha256']==sha((OUT/'run-side.py').read_bytes())
 assert r['script_sha256']==C['tools']['scripts/copy-text-screen-v3.py']==sc['tool_sha256']
 assert r['command'][:5]==['nice','-n','10','python3','-I'] and r['command'][6:]==[C['temporary_trees'][side],*C['population']]
 assert all(r[k]==v for k,v in request.items())
 data=(OUT/(side+'.out')).read_bytes();assert sha(data)==r['output_sha256'] and len(data)==r['bytes'] and data.decode().splitlines()[0]==r['first_line']
 side_runs[side]=r
for path,digest in C['tools'].items():
 data=(ROOT/path).read_bytes();assert sha(data)==digest
 assert (OUT/'tools'/(Path(path).name+'.txt')).read_bytes()==data
 for pin in [C['base'],C['head']]:assert git('show',pin+':'+path)==data
for path in ['devtools/seyoon/pairdiff.py','devtools/seyoon/declfreeze.py','scripts/style_lint.py','scripts/campaign_style_lint.py']:
 data=(ROOT/path).read_bytes()
 for pin in [C['base'],C['head']]:assert git('show',pin+':'+path)==data
 if path.endswith('pairdiff.py'):(OUT/'tools/pairdiff.py.txt').write_bytes(data)
old_inventory=read(OUT/'prior-full25-inventories-before.json');preserved=[]
for old in old_inventory:
 folder=Path(old['folder']);files=[dict(path=str(p.relative_to(folder)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(folder.rglob('*')) if p.is_file()]
 assert files==old['files'] and len(files)==old['file_count'],str(folder)
 preserved.append(dict(folder=str(folder),files=len(files),all_original_paths_and_bytes_preserved=True))
wt=Path(C['actual_worktree']);actual=git('rev-parse','HEAD',wt=wt).decode().strip();remote=git('rev-parse',C['explicit_pushed_ref'],wt=wt).decode().strip();status=git('status','--porcelain','--untracked-files=no',wt=wt).decode()
assert actual==remote==C['head'] and status==''
assert git('diff',C['head'],'HEAD','--','*.lean',wt=wt)==b''
# Intentionally detached is observed, never changed. Explicit pushed ref is the provenance test.
branch=subprocess.run(['git','-C',str(wt),'symbolic-ref','--quiet','--short','HEAD'],stdout=subprocess.PIPE)
assert branch.returncode==1 and branch.stdout==b''
events=[json.loads(x) for x in (OUT/'lock-events.jsonl').read_text().splitlines()]
assert len(events)==10 and [x['event'] for x in events]==['waiting','acquired','launched','completed','released']*2
assert [x['side'] for x in events]==['base']*5+['head']*5
assert events[3]['exit']==events[8]['exit']==0 and events[4]['utc']<events[5]['utc']<events[7]['utc']
assert side_runs['base']['end_utc']<=events[4]['utc']<side_runs['head']['start_utc']
queued=read(OUT/'head-queue-release.json');assert queued['base_actual_exit']==0 and queued['base_released_before_HEAD_command'] and queued['base_receipt_sha256']==sha((OUT/'base-run.json').read_bytes()) and queued['head_capture_sha256']==sha((OUT/'head-capture.json').read_bytes())
for side in ['base','head']:
 observed=read(OUT/(side+'-running-process.json'));a=observed['active_screen_processes'];assert len(a)==1 and int(a[0]['pid'])==side_runs[side]['pid'] and a[0]['nice']=='10' and observed['lock_files']['pid'].strip()==a[0]['pid']
processes=[]
for line in subprocess.check_output(['ps','-axo','pid=,ppid=,etime=,ni=,command='],text=True).splitlines():
 a=line.split(None,4)
 if len(a)==5 and Path(a[4].split()[0]).name.lower().startswith('python') and 'copy-text-screen-v3.py' in a[4]:processes.append(dict(zip(['pid','ppid','elapsed','nice','command'],a)))
assert not processes,processes
lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen';assert not lock.exists()
assert read(OUT/'source-freeze.json')['all25_source_checks_pass']
assert read(OUT/'source-QA-run.json')['exit']==0
lint=read(OUT/'lint-results.json');assert lint['fresh_full25_unmodified_CLIs'] and all(not d['normalized_new'] and not d['normalized_gone'] for d in lint['delta'].values())
assert len(read(OUT/'proof-header-controls.json'))==10
save('RUNNING-JOBS.json',dict(status='COMPLETE: both actual fresh25 executions exited0 and released the shared lock; owned PIDs absent',base_session=64133,head_queue_session=96949,base_pid=side_runs['base']['pid'],head_pid=side_runs['head']['pid']))
verification=dict(verified_utc=now(),result='PASS source/screen-provenance checks; no Lean executed by this task',base=C['base'],head=C['head'],complete_sources=len(selected),source_files=selected,source_tool_and_pin_checks=True,unmodified_v3=True,all_25_per_side_fresh_execution=True,both_exits=0,serial_lock_events=events,both_observed_nice=10,no_remaining_screen_processes=processes,shared_lock_absent=True,actual_source_worktree=dict(path=str(wt),head=actual,explicit_pushed_ref=C['explicit_pushed_ref'],explicit_pushed_head=remote,tracked_status=status,intentionally_detached=True),historical_full25_folders=preserved,scope='Read-only Git/source checks and own evidence/scratch writes only. No source/Git/Lean/cache modification. No global semantic/debt/gate verdict.')
save('verification.json',verification)
print(json.dumps(dict(result=verification['result'],source_files=len(selected),historical_folders=preserved,shared_lock_absent=True,current_head=actual),indent=2))
