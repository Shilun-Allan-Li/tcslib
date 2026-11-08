from pathlib import Path
import base64,collections,datetime,hashlib,io,json,os,subprocess,tarfile,time
OUT=Path(__file__).resolve().parent
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OLD=ROOT/'campaign/fills/mig1/landing/screen-current25-final'
C=json.loads((OUT/'BASE-CAPTURE-MASTER.json').read_text());SC=json.loads((OUT/'base-capture.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest();now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(p):return json.loads(p.read_text())
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*a):return subprocess.run(['git','-C',str(ROOT),*a],check=True,stdout=subprocess.PIPE).stdout
r=read(OUT/'base-run.json');assert r['exit']==0 and r['fresh_execution'] and r['full_population']==25 and r['source_commit']==C['base']==SC['commit']
assert r['side_capture_sha256']==sha((OUT/'base-capture.json').read_bytes()) and r['orchestrator_sha256']==sha((OUT/'run-side.py').read_bytes()) and r['script_sha256']==SC['tool_sha256']
assert r['output_sha256']==sha((OUT/'base.out').read_bytes())
ns={'__name__':'base_parse_only','__file__':str(OUT/'analyze-screens.py')};exec(compile((OUT/'analyze-screens.py').read_text(),str(OUT/'analyze-screens.py'),'exec'),ns);rows,summary=ns['parse']('base')
old=[dict(a=x['target'],b=x['source'],shared=x['shared_chars'],denominator=x['source_body_chars'],printed_percent=x['rounded_percent'],kind=x['kind'],cross_file=x['cross_file']) for x in read(OLD/'base-all-candidates.json')]
key=lambda x:(x['a'],x['b']);a={key(x):x for x in old};b={key(x):x for x in rows}
d=dict(previous_BASE=C['previous_base'],current_BASE=C['base'],previous_summary=read(OLD/'candidate-summary.json')['base'],current_summary=summary,new=[b[k] for k in sorted(b.keys()-a.keys())],gone=[a[k] for k in sorted(a.keys()-b.keys())],changed=[dict(previous=a[k],current=b[k]) for k in sorted(a.keys()&b.keys()) if a[k]!=b[k]],scope='Every raw fresh current BASE delta versus historical API1160 BASE on exact same25. No earlier screen adopted; HEAD not analyzed.')
assert not d['changed']
labels={'Finite.lean::exists_first_entry_of_fixed','Catalog.lean::redirectTM_spaceUsedByTape','Wrappers.lean::redirectTM_spaceUsedByTape'}
assert all({x['a'],x['b']}&labels for x in d['new']+d['gone'])
save('BASE-upstream-pair-delta.json',d)
cmd=['python3','-I',str(ROOT/'devtools/seyoon/pairdiff.py'),str(OUT/'base.out'),str(OLD/'base.out')];tick=time.time();start=now();q=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE);(OUT/'canonical-pairdiff-BASE-upstream.out').write_bytes(q.stdout);(OUT/'canonical-pairdiff-BASE-upstream.stderr.out').write_bytes(q.stderr);save('canonical-pairdiff-BASE-upstream-run.json',dict(command=cmd,start_utc=start,end_utc=now(),seconds=time.time()-tick,exit=q.returncode,tool_sha256=sha((ROOT/'devtools/seyoon/pairdiff.py').read_bytes()),stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr)));assert q.returncode==0
index={x['label']:x for x in read(OUT/'base-index.json')};weights={p:dict(incident_rows=0,shared_chars=0,outgoing_rows=0,incoming_rows=0) for p in C['population']};matrix=collections.defaultdict(lambda:dict(rows=0,shared_chars=0))
for x in rows:
 p=index[x['a']]['path'];q=index[x['b']]['path']
 for path in {p,q}:weights[path]['incident_rows']+=1;weights[path]['shared_chars']+=x['shared']
 weights[p]['outgoing_rows']+=1;weights[q]['incoming_rows']+=1;matrix[(p,q,x['kind'])]['rows']+=1;matrix[(p,q,x['kind'])]['shared_chars']+=x['shared']
save('BASE-weighted-candidate-accounting.json',dict(summary=summary,files=[dict(path=p,**v) for p,v in sorted(weights.items(),key=lambda x:(-x[1]['shared_chars'],x[0]))],ordered_file_pair_matrix=[dict(a=p,b=q,kind=k,**v) for (p,q,k),v in sorted(matrix.items())],interpretation='All files/buckets retained uncapped. Inclusive weights overlap; directed textual rows are not semantic duplicate/declaration/debt counts. BASE evidence does not accept any retained candidate.'))
# Exact current BASE provenance; HEAD is intentionally outside this verification.
archive=base64.b64decode((OUT/'base.tar.base64.txt').read_bytes());assert sha(archive)==SC['archive_sha256']==C['sides']['base']['archive_sha256'] and len(archive)==C['sides']['base']['archive_bytes']
verified=[]
with tarfile.open(fileobj=io.BytesIO(archive),mode='r:') as tf:
 members={m.name:m for m in tf.getmembers() if m.isfile()};assert set(members)==set(C['population'])
 for x in SC['files']:
  path=x['path'];data=git('show',C['base']+':'+path);assert git('rev-parse',C['base']+':'+path).decode().strip()==x['blob'];assert sha(data)==x['sha256'] and len(data)==x['bytes'];assert tf.extractfile(members[path]).read()==data==(OUT/'inputs/base'/(path+'.txt')).read_bytes()==(Path(SC['tree'])/path).read_bytes();data.decode('utf-8');verified.append(x)
tool=ROOT/'scripts/copy-text-screen-v3.py';assert sha(tool.read_bytes())==SC['tool_sha256'] and git('show',C['base']+':scripts/copy-text-screen-v3.py')==tool.read_bytes()==(OUT/'tools/copy-text-screen-v3.py.txt').read_bytes()
assert git('diff',C['merged_API'],C['base'],'--','*.lean')==b''
preserved=[]
for gen in read(OUT/'historical-screen-generations-before.json'):
 folder=Path(gen['folder']);files=[dict(path=str(p.relative_to(folder)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for p in sorted(folder.rglob('*')) if p.is_file()];assert files==gen['files'];preserved.append(dict(folder=str(folder),files=len(files),paths_and_bytes_unchanged=True))
other=read(OUT/'historical-other-screen-artifacts-before.json')
for x in other:
 data=(ROOT/x['path']).read_bytes();assert len(data)==x['bytes'] and sha(data)==x['sha256']
events=[json.loads(x) for x in (OUT/'lock-events.jsonl').read_text().splitlines()];base_events=[x for x in events if x['side']=='base'];assert [x['event'] for x in base_events]==['waiting','acquired','launched','completed','released'] and base_events[3]['exit']==0
observed=read(OUT/'base-running-process.json');assert len(observed['active_screen_processes'])==1 and int(observed['active_screen_processes'][0]['pid'])==r['pid'] and observed['active_screen_processes'][0]['nice']=='10' and observed['lock_files']['pid'].strip()==str(r['pid'])
active=[]
for line in subprocess.check_output(['ps','-axo','pid=,ppid=,etime=,ni=,command='],text=True).splitlines():
 x=line.split(None,4)
 if len(x)==5 and Path(x[4].split()[0]).name.lower().startswith('python') and 'copy-text-screen-v3.py' in x[4]:active.append(dict(zip(['pid','ppid','elapsed','nice','command'],x)))
assert all(int(x['pid'])!=r['pid'] for x in active)
lock=Path(os.environ['TCSLIB_SCRATCH'])/'locks/screen'
save('BASE-verification.json',dict(utc=now(),result='PASS current BASE25 source/screen provenance',base=C['base'],full_verified_sources=25,files=verified,fresh_execution_exit=0,output_sha256=r['output_sha256'],unmodified_v3=True,observed_nice=10,own_lock_released=True,base_lock_events=base_events,owned_BASE_pid_absent=True,active_screens_at_verification=active,shared_lock_absent_at_verification=not lock.exists(),preserved_generations=preserved,other_historical_artifacts_preserved=len(other),HEAD_status='Not certified; final clean committed pushed pin and separate fresh HEAD run required.'))
print(json.dumps(dict(actual_BASE=summary,actual_exit=r['exit'],seconds=r['seconds'],upstream_delta=dict(new=len(d['new']),gone=len(d['gone']),changed=len(d['changed'])),source_files_verified=25,preserved_generations=[x['files'] for x in preserved],other_historical_screen_artifacts=len(other),BASE_lock_released=True,active_screen_processes=active,HEAD='NOT analyzed; final pushed pin required'),indent=2));print((OUT/'canonical-pairdiff-BASE-upstream.out').read_text())
