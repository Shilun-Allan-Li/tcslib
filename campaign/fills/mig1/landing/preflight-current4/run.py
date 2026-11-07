from pathlib import Path
import os,subprocess,json,hashlib,time,datetime,re
r=Path.cwd();s=Path(os.environ['TCSLIB_SCRATCH']);wt=s/'wt-epad';out=r/'campaign/fills/mig1/landing/preflight-current4';parent=s/'oleans-mig1-preflight-current3';tree=s/'oleans-mig1-preflight-current4';assert parent.exists() and not tree.exists()
subprocess.run(['cp','-cR',str(parent),str(tree)],check=True)
def inventory(p):return {str(f.relative_to(p)):f.stat().st_size for f in p.rglob('*.olean')}
a=inventory(parent);b=inventory(tree);assert a==b and len(a)>=894
(out/'clone-verification.json').write_text(json.dumps({'whole_relative_olean_paths_sizes_identical':True,'olean_count':len(a),'parent':str(parent),'clone':str(tree),'no_splice':True},indent=2)+'\n')
order=(out/'order.txt').read_text().splitlines();rows=[];pins={f:hashlib.sha256((wt/f).read_bytes()).hexdigest() for f in order}
for rel in order:
 source=wt/rel;data=source.read_bytes();name=source.stem;(out/(name+'.lean.txt')).write_bytes(data)
 for ext in ['.olean','.ilean','.c','.trace']:(tree/Path(rel).with_suffix(ext)).unlink(missing_ok=True)
 cmd=['bash',str(r/'devtools/seyoon/leanelab-o.sh'),str(wt),str(tree),rel,str(tree)];start=time.time();c=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);raw=out/(name+'.out');raw.write_bytes(c.stdout)
 row={'source':rel,'source_sha256':hashlib.sha256(data).hexdigest(),'source_unchanged_during_compile':hashlib.sha256(source.read_bytes()).hexdigest()==pins[rel],'command':cmd,'seconds':time.time()-start,'exit':c.returncode,'errors':len(re.findall(rb'(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:',c.stdout)),'output_sha256':hashlib.sha256(c.stdout).hexdigest(),'output_olean_sha256':hashlib.sha256((tree/Path(rel).with_suffix('.olean')).read_bytes()).hexdigest() if (tree/Path(rel).with_suffix('.olean')).exists() else None}
 (out/(name+'-run.json')).write_text(json.dumps(row,indent=2)+'\n');rows.append(row);print(json.dumps({'module':name,'exit':row['exit'],'errors':row['errors'],'seconds':round(row['seconds'],2)}),flush=True)
 if c.returncode or row['errors'] or not row['source_unchanged_during_compile']:
  print(c.stdout.decode(errors='replace')[-5000:],flush=True);raise SystemExit(1)
assert all(hashlib.sha256((wt/f).read_bytes()).hexdigest()==h for f,h in pins.items())
(out/'receipt.json').write_text(json.dumps({'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'modules':5,'errors':0,'failures':0,'all_sources_stable':True,'complete_overlay':str(tree),'full_source_fresh_chain':rows,'scope':'fresh5-module tail after complete current3 twelve-module chain; no new full downstream replay or gate closure claimed'},indent=2)+'\n');print('All5 actual tailmodules PASS; no full downstream replay claim.',flush=True)
