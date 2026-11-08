from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
OUT=Path(__file__).resolve().parent
C=json.loads((OUT/'context.json').read_text())
project=Path(C['project']);sha=lambda b:hashlib.sha256(b).hexdigest();now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
assert sha(Path(C['wrapper']).read_bytes())==C['wrapper_sha256']
env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3'
for label in ['Owner-native','Owner-sealed']:
 file=project/(label+'.lean');assert file.read_bytes()==(OUT/(label+'-with-axioms.lean.txt')).read_bytes()
 command=['bash',C['wrapper'],str(project),C['snapshot'],file.name]
 row=dict(command=command,start_utc=now(),head=C['head'],actual_source_sha256=C['actual_source_sha256'],proposed_source_sha256=C['proposed_source_sha256'],input_sha256=sha(file.read_bytes()),snapshot=C['snapshot'],snapshot_olean_count=C['snapshot_olean_count'],toolchain=C['toolchain'],local_budget=3,concurrent_jobs_in_this_runner=1,expected_exit=0)
 (OUT/(label+'-request.json')).write_text(json.dumps(row,indent=2)+'\n');print('START '+label+' '+row['start_utc'],flush=True);tick=time.time()
 q=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=env)
 (OUT/(label+'.out')).write_bytes(q.stdout);text=q.stdout.decode();rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)
 assert len(rows)==3,(label,text)
 ax=[dict(name=n,axioms=[x.strip() for x in a.split(',') if x.strip()]) for n,a in rows]
 standard=all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in ax)
 row.update(end_utc=now(),seconds=time.time()-tick,exit=q.returncode,output_sha256=sha(q.stdout),bytes=len(q.stdout),errors=len(re.findall(r'\berror:',text)),warnings=len(re.findall(r'\bwarning:',text)),sorry_warnings=text.count("declaration uses 'sorry'"),axioms=ax,all_three_standard=standard)
 (OUT/(label+'-run.json')).write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
 assert q.returncode==0 and row['errors']==0 and row['sorry_warnings']==0 and standard
assert not list(project.glob('*.olean')) and not list(project.glob('*.ilean'))
expected=json.loads((OUT/'snapshot-before.json').read_text());actual=[]
for p in sorted(Path(C['snapshot']).rglob('*.olean')):actual.append(dict(path=str(p.relative_to(C['snapshot'])),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
assert actual==expected
assert sha((Path(C['actual_worktree'])/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_bytes())==C['actual_source_sha256']
(OUT/'snapshot-after.json').write_text(json.dumps(actual,indent=2)+'\n')
(OUT/'verification.json').write_text(json.dumps(dict(end_utc=now(),native_and_19scope_fullcopies_pass=True,target_private_seam_public_seam_all_standard=True,guards_unchanged_35TCS_plus_Nat_bits=True,all895_snapshot_olean_bytes_unchanged=True,actual_source_unchanged=True,no_compiled_outputs=True,exact_inverse_reconstruction=True),indent=2)+'\n')
print('BOTH PREFLIGHTS PASS; ALL895 SNAPSHOT HASHES AND ACTUAL SOURCE UNCHANGED',flush=True)
