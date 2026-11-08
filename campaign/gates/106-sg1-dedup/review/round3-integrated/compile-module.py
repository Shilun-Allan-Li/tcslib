from pathlib import Path
import json,hashlib,subprocess,datetime,time,re,sys,os
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4];c=json.loads((OUT/'context.json').read_text());rel=sys.argv[1];tag=Path(rel).stem;wt=Path(c['worktree']);ov=Path(c['overlay']);src=wt/rel
assert rel in c['source_pins'] and hashlib.sha256(src.read_bytes()).hexdigest()==c['source_pins'][rel]
log=OUT/(tag+'-compile.out');receipt=OUT/(tag+'-compile-run.json');assert not log.exists() and not receipt.exists()
module=ov/rel.removesuffix('.lean');removed=[]
for p in sorted(module.parent.glob(module.name+'.*')):
 assert p.is_file() or p.is_symlink();row={'path':str(p),'bytes':p.stat().st_size,'inode':p.stat().st_ino,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()};p.unlink();row['unlinked']=not p.exists();removed.append(row)
assert not module.with_suffix('.olean').exists()
command=['bash',str(ROOT/'devtools/seyoon/leanelab-o.sh'),str(wt),str(ov),rel,str(ov)]
start=time.time();row={'command':command,'start_utc':datetime.datetime.fromtimestamp(start,datetime.timezone.utc).isoformat(),'source_sha256':c['source_pins'][rel],'complete_overlay':str(ov),'snapshot_input':c['snapshot'],'unlinked_before_compile':removed,'local_budget':os.environ.get('TCSLIB_LEAN_SLOTS'),'no_outer_lock':True,'compiled_order':c['compile_order']}
(OUT/(tag+'-compile-request.json')).write_text(json.dumps(row,indent=2)+'\n')
r=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);log.write_bytes(r.stdout);text=r.stdout.decode(errors='replace');output=module.with_suffix('.olean');row.update(exit=r.returncode,seconds=time.time()-start,errors=len(re.findall(r'^.*:\d+:\d+: error(?:\([^)]*\))?:',text,re.M)),warnings=len(re.findall(r'^.*:\d+:\d+: warning:',text,re.M)),output_log_sha256=hashlib.sha256(r.stdout).hexdigest(),source_still_exact=hashlib.sha256(src.read_bytes()).hexdigest()==c['source_pins'][rel],olean_written=output.is_file())
if output.is_file():row['olean']={'path':str(output),'bytes':output.stat().st_size,'sha256':hashlib.sha256(output.read_bytes()).hexdigest()}
receipt.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({k:row[k] for k in ['exit','seconds','errors','warnings','source_still_exact','olean_written']},indent=2))
if r.returncode:print('\n'.join(l for l in text.splitlines() if ' error' in l));raise SystemExit(r.returncode)
assert row['source_still_exact'] and row['olean_written']
