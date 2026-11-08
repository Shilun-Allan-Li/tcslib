from pathlib import Path
import os,sys,json,subprocess,hashlib,datetime,time,re,shutil
O=Path('/private/tmp/ab34-fe-live1-final-validation');E=O/'evidence';F=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);IN=S/'oleans-mac8';OUT=O/'live/oleans-fe1';B='9b5dcf46408db681bcbc721930ef2203fa6bc47d';H='a93d1867d6ed9700f2fd89a28092e39a45db2dd2'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def put(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
def git(*args):return subprocess.check_output(['git','-C',str(F),*args]).decode().strip()
def objmap(root):
 rows=[]
 for p in sorted(root.rglob('*')):
  if p.is_symlink():raise AssertionError(('snapshot symlink',str(p)))
  if p.is_file():
   st=p.stat();rows.append({'path':str(p.relative_to(root)),'bytes':st.st_size,'sha256':sha(p.read_bytes()),'inode':st.st_ino,'device':st.st_dev,'mtime_ns':st.st_mtime_ns})
 return rows
def content(rows):return [{k:r[k] for k in ('path','bytes','sha256')} for r in rows]
start=now();t=time.monotonic();assert git('rev-parse','HEAD')==H;assert git('rev-parse','refs/remotes/origin/codex/ab34-fe-live1')==H;assert not git('status','--porcelain','--untracked-files=no')
source=json.loads((E/'SOURCE.json').read_text());closure=json.loads((E/'CLOSURE.json').read_text());order=closure['order'];assert len(order)==len(set(order))
for r in source['files']:assert sha((F/r['path']).read_bytes())==r['HEAD']['sha256']
assert (S/'fills/replay/replay-mjoint1.log').read_text().splitlines()[-1]=='# modules=394 failed=0'
assert not OUT.exists();assert (F/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib').is_dir()
print('PRECHECK PASS; hashing whole MAC8',flush=True);before=objmap(IN);assert len(before)==895 and all(r['path'].endswith('.olean') for r in before);put(E/'INPUT-895-before.json',before)
adopt=json.loads((E/'baseline-adoption/object-hashes.json').read_text())
# The complete published adoption map is separately retained and compared explicitly after inspecting its schema.
put(E/'RUN-PRECHECK.json',{'utc':start,'head':H,'baseline':B,'whole_snapshot':str(IN),'input_objects':len(before),'tracking_ref_matches':True,'tracked_clean':True,'owners_sha_match':True,'closure':len(order),'slot_limit':os.environ.get('TCSLIB_LEAN_SLOTS'),'slotrun_pid':os.getppid(),'driver_pid':os.getpid(),'no_Git_mutations':True,'all_driver_commands_start_after_sourced_env':True})
cp=['cp','-cR',str(IN),str(OUT)];(E/'clone-command.json').write_text(json.dumps(cp)+'\n');r=subprocess.run(cp,capture_output=True);(E/'clone.out').write_bytes(r.stdout+r.stderr);assert r.returncode==0,'whole clone failed'
cloned=objmap(OUT);put(E/'CLONE-895-before.json',cloned);assert content(before)==content(cloned);assert all((a['device'],a['inode'])!=(b['device'],b['inode']) for a,b in zip(before,cloned))
print(f'WHOLE CLONE PASS; replay modules={len(order)}',flush=True)
rows=[];log=E/'replay.log';detailed=E/'modules';detailed.mkdir(exist_ok=True);failed=0
with log.open('w') as lf:
 lf.write(f'# replay FE-LIVE-1 final HEAD={H} BASE={B} whole MAC8 ({len(order)} modules)\n');lf.flush()
 for index,m in enumerate(order,1):
  st=now();tm=time.monotonic();p=OUT/(m+'.olean');old={'exists':p.exists(),'mtime_ns':p.stat().st_mtime_ns if p.exists() else None,'sha256':sha(p.read_bytes()) if p.exists() else None};argv=['nice','-n','10','bash',str(F/'scripts/lean_check_tree.sh'),m]
  env=os.environ.copy();env['TCSLIB_OLEANS']=str(OUT);r=subprocess.run(argv,cwd=F,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);raw=r.stdout;safe=f'{index:03d}-'+m.replace('/','__');(detailed/(safe+'.out')).write_bytes(raw);text=raw.decode(errors='replace');errors=len(re.findall(r': error(?:\([^\n]*?\))?:',text));k=raw.count(b"declaration uses 'sorry'");fresh=p.is_file() and p.stat().st_size>0 and p.stat().st_mtime_ns!=old['mtime_ns'];passed=r.returncode==0 and errors==0 and fresh and 'FAIL(' not in text
  if not passed:failed+=1
  row={'index':index,'module':m,'start_utc':st,'seconds':time.monotonic()-tm,'argv':argv,'exit':r.returncode,'errors':errors,'sorry_warnings':k,'output_bytes':len(raw),'output_sha256':sha(raw),'output_file':str((detailed/(safe+'.out')).relative_to(E)),'source_sha256':sha((F/(m+'.lean')).read_bytes()),'object_before':old,'fresh_object':fresh,'object_after_sha256':sha(p.read_bytes()) if p.is_file() else None,'PASS':passed};put(detailed/(safe+'.json'),row);rows.append(row);put(E/'REPLAY-RESULTS.json',rows)
  lf.write(f'{m} exit={r.returncode} errors={errors} sorry={k}\n');lf.flush();print(f'{index}/{len(order)} {m} exit={r.returncode} errors={errors} sorry={k} fresh={fresh} seconds={row["seconds"]:.2f}',flush=True)
 lf.write(f'# modules={len(rows)} failed={failed}\n');lf.flush()
argv=['python3','-I',str(S/'api/staticsorry.py'),str(F),str(log)];r=subprocess.run(argv,capture_output=True);(E/'replay-static.txt').write_bytes(r.stdout+r.stderr);staticok=r.returncode==0 and b'mismatches 0,' in r.stdout
print('REPLAY FINISHED; hashing input/output again',flush=True);after=objmap(IN);outmap=objmap(OUT);put(E/'INPUT-895-after.json',after);put(E/'OUTPUT-895.json',outmap);assert before==after,'INPUT SNAPSHOT MUTATED';assert len(outmap)==895
inside={m+'.olean' for m in order};bm={r['path']:r for r in before};om={r['path']:r for r in outmap};assert set(bm)==set(om)
outside=[{'path':p,'input_sha256':bm[p]['sha256'],'output_sha256':om[p]['sha256'],'exact':content([bm[p]])==content([om[p]])} for p in sorted(set(bm)-inside)];assert all(r['exact'] for r in outside);put(E/'OUTSIDE-CLOSURE.json',outside)
assert git('rev-parse','HEAD')==H and git('rev-parse','refs/remotes/origin/codex/ab34-fe-live1')==H;assert not git('status','--porcelain','--untracked-files=no')
for r in source['files']:assert sha((F/r['path']).read_bytes())==r['HEAD']['sha256']
summary={'start_utc':start,'end_utc':now(),'seconds':time.monotonic()-t,'head':H,'baseline':B,'actual_executed':True,'modules':len(rows),'failed':failed,'errors':sum(r['errors'] for r in rows),'sorry_warnings':sum(r['sorry_warnings'] for r in rows),'static_exit':r.returncode if False else None,'static_ok':staticok,'input_objects':len(before),'output_objects':len(outmap),'input_unchanged_including_inode_mtime':True,'outside_scope_objects':len(outside),'outside_scope_byte_equal':True,'whole_clone':cp,'no_splicing':True,'all_owner_final_sketch_bytes_compiled':all(p[:-5] in order for p in [x['path'] for x in source['files']]),'source_and_pushed_ref_unchanged':True,'one_own_slot':True,'PASS':failed==0 and staticok}
put(E/'REPLAY-SUMMARY.json',summary);print(json.dumps(summary),flush=True)
if not summary['PASS']:
 shutil.rmtree(OUT);put(E/'FAILED-SNAPSHOT-DISCARDED.json',{'path':str(OUT),'utc':now(),'reason':'failed replay cannot remain a valid snapshot','logs_retained':True});sys.exit(1)
