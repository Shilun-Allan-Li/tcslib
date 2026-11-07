"""Maintainer-owned offline reconciliation. Delivered code is never imported/executed."""
from pathlib import Path
import sys,re,json,hashlib,subprocess,os,datetime,importlib.util
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[5];incoming=out.parent;delivery=incoming/'extracted/fill-mig1-mega-r2';ev=delivery/'evidence';wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad';lineage=json.loads((incoming/'verified-lineage.json').read_text());H=lambda b:hashlib.sha256(b.encode() if isinstance(b,str) else b).hexdigest();env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');commands=[]
spec=importlib.util.spec_from_file_location('P',root/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
manifest=json.loads((incoming/'payload-manifest.json').read_text());pm={r['local_path']:r for r in manifest};verified={}
def read(p):
 b=p.read_bytes();key=str(p.relative_to(incoming/'extracted'));r=pm[key];assert len(b)==r['bytes'] and H(b)==r['sha256'],key;verified[key]={'sha256':H(b),'bytes':len(b)};return b

def git(*args):
 c=['git','-C',str(wt),*args];commands.append(c);return subprocess.run(c,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout
commits={'base':lineage['base'],'prior':lineage['prior_delivery'],'mid':lineage['sweep2_head'],'head':lineage['verified_head']}
for c in commits.values():assert git('rev-parse','--verify',c+'^{commit}').decode().strip()==c;git('cat-file','-e',c+'^{commit}')
assert git('rev-parse',lineage['delivery_ref']).decode().strip()==commits['head']
def tree(c):
 rows={}
 for line in git('ls-tree','-r',c,'--','TCSlib','TCSlib.lean','lean-toolchain','lake-manifest.json','lakefile.lean').decode().splitlines():
  meta,p=line.split('\t',1);mode,kind,oid=meta.split();assert kind=='blob';rows[p]={'mode':mode,'oid':oid}
 return rows
trees={stage:tree(c) for stage,c in commits.items()};changed=git('diff','--name-only',commits['mid'],commits['head']).decode().splitlines();prim='TCSlib/Complexity/TuringMachine/Build/Primitives.lean';assert changed==[prim]
# Read all unique requested Git blobs via Git's native read-only batch protocol.
oids=set(r['oid'] for st in ['mid','head'] for p,r in trees[st].items() if p.endswith('.lean') or p in ['lean-toolchain','lake-manifest.json']);oids|={r['oid'] for p,r in trees['base'].items() if p in read(ev/'screens/screen-population.txt').decode().splitlines()};ordered=sorted(oids);c=['git','-C',str(wt),'cat-file','--batch'];commands.append(c);r=subprocess.run(c,env=env,input=''.join(x+'\n' for x in ordered).encode(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True);data=r.stdout;cursor=0;objects={}
for oid in ordered:
 e=data.index(b'\n',cursor);header=data[cursor:e].decode().split();assert header[:2]==[oid,'blob'];n=int(header[2]);b=data[e+1:e+1+n];assert data[e+1+n:e+2+n]==b'\n';assert hashlib.sha1(b'blob '+str(n).encode()+b'\0'+b).hexdigest()==oid;objects[oid]=b;cursor=e+2+n
assert cursor==len(data)
source={stage:{p:objects[r['oid']].decode() for p,r in trees[stage].items() if r['oid'] in objects and p.endswith('.lean')} for stage in ['base','mid','head']}
# Source snapshots supplied for11owned homes match actual imported head objects.
owned=[]
for p in (delivery/'source/TCSlib').rglob('*.lean.txt'):
 rel=str(p.relative_to(delivery/'source')).removesuffix('.txt');b=read(p);assert b==objects[trees['head'][rel]['oid']];owned.append(rel)
assert len(owned)==11
# The trusted static method counts admitted top-level declaration blocks, with comments/strings removed.
dec=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|instance|example|structure|inductive|class)\b',re.M)
def static(s):
 c=P.clean(s);c=re.sub(r'"(?:\\.|[^"\\])*"',lambda m:'\n'*m[0].count('\n')+' ',c);starts=[x.start() for x in dec.finditer(c)]+[len(c)];rows=[]
 for a,b in zip(starts,starts[1:]):
  hits=list(re.finditer(r'\b(?:sorry|admit)\b',c[a:b]))
  if hits:rows.append({'declaration_line':c.count('\n',0,a)+1,'admission_lines':[c.count('\n',0,a+m.start())+1 for m in hits]})
 return rows
# Every TCSlib import is parsed independently from the actual head source.
graph={p.removesuffix('.lean'):[] for p in source['head'] if p.startswith('TCSlib')}
for p,s in source['head'].items():
 mod=p.removesuffix('.lean')
 if mod not in graph:continue
 for line in P.clean(s).splitlines():
  m=re.match(r'^\s*(?:public\s+)?import\s+(.*)$',line)
  if m:graph[mod]+=[x.replace('.','/') for x in m[1].split() if x=='TCSlib' or x.startswith('TCSlib.')]
missing_imports=sorted({x for ds in graph.values() for x in ds if x not in graph});assert not missing_imports
rowpat=re.compile(r'^(\S+) start=(\S+) end=(\S+) secs=(\d+) maxrss_kb=(\d+) exit=(\d+) errors=(\d+) sorry_warnings=(\d+)$')
allrows={};summaries={};discrepancies=[]
for folder,stage,expected in [('final-sweep-2','mid',641),('final-sweep-3-downstream-of-Primitives','head',223)]:
 d=ev/'logs'/folder;text=read(d/'summary.log').decode();lines=text.splitlines();h=re.fullmatch(r'# sweep of (\d+) modules at ([0-9a-f]{40}) dirty=(\d+) start (\S+)',lines[0]);assert h and int(h[1])==expected and h[2]==commits[stage] and h[3]=='0';tail=re.fullmatch(r'# modules=(\d+) failed=(\d+) end (\S+)',lines[-1]);assert tail and int(tail[1])==expected and tail[2]=='0';rows=[];last=None
 for line in lines[1:-1]:
  m=rowpat.fullmatch(line);assert m,line;mod,start,end,secs,rss,exit,errors,sorry=m.groups();secs,rss,exit,errors,sorry=map(int,[secs,rss,exit,errors,sorry]);rawpath=d/'raw'/(mod.replace('/','.')+'.out');timepath=rawpath.with_name(rawpath.name+'.time');raw=read(rawpath);time=read(timepath);rtext=raw.decode();tt=time.decode();actual_errors=len(re.findall(r'error:',rtext));actual_sorry=rtext.count("declaration uses 'sorry'");actual_rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tt)[1]);actual_exit=int(re.search(r'Exit status: (\d+)',tt)[1]);command=re.search(r'Command being timed: "(.*?)"',tt)[1];assert command=='nice -n 10 bash scripts/lean_check_tree.sh '+mod
  sourcepath=mod+'.lean';body=source[stage][sourcepath];admissions=static(body);mismatch=[]
  if (exit,errors,sorry,rss)!=(actual_exit,actual_errors,actual_sorry,actual_rss):mismatch.append('summary/raw/time metadata mismatch')
  if sorry!=len(admissions):mismatch.append('static/raw admission mismatch')
  t0=datetime.datetime.fromisoformat(start.replace('Z','+00:00'));t1=datetime.datetime.fromisoformat(end.replace('Z','+00:00'))
  if abs((t1-t0).total_seconds()-secs)>1:mismatch.append('start/end/seconds mismatch')
  if last and t0<last:mismatch.append('summary order time overlaps')
  last=t1
  if mismatch:discrepancies.append({'sweep':folder,'module':mod,'problems':mismatch,'static':len(admissions),'raw':sorry})
  rows.append({'module':mod,'start':start,'end':end,'seconds':secs,'maxrss_kb':rss,'reported_exit':exit,'time_receipt_exit':actual_exit,'reported_errors':errors,'raw_errors':actual_errors,'reported_sorry_warnings':sorry,'raw_sorry_warnings':actual_sorry,'static_admitted_declarations':len(admissions),'admission_locations':admissions,'source_git_blob':trees[stage][sourcepath]['oid'],'source_sha256':H(body),'raw_path':str(rawpath.relative_to(delivery)),'raw_sha256':H(raw),'time_path':str(timepath.relative_to(delivery)),'time_sha256':H(time),'problems':mismatch})
 assert len(rows)==expected and len({r['module'] for r in rows})==expected;expectedfiles={mod.replace('/','.')+'.out'+suffix for mod in [r['module'] for r in rows] for suffix in ['', '.time']};assert {p.name for p in (d/'raw').iterdir()}==expectedfiles
 static_receipt=read(d/'static-vs-lean.txt').decode();assert static_receipt.strip()==f'modules {expected} static {sum(r["static_admitted_declarations"] for r in rows)} lean {sum(r["raw_sorry_warnings"] for r in rows)} mismatches []'
 summaries[folder]={'pinned_source_commit':commits[stage],'module_count':len(rows),'raw_errors':sum(r['raw_errors'] for r in rows),'nonzero_time_exits':sum(r['time_receipt_exit']!=0 for r in rows),'static_admissions':sum(r['static_admitted_declarations'] for r in rows),'raw_sorry_warnings':sum(r['raw_sorry_warnings'] for r in rows),'start':h[4],'end':tail[3],'summary_sha256':H(text),'source_claim':'Producer supplied evidence reconciled offline; no execution by reviewer.'};allrows[folder]=rows;(out/(folder+'-module-map.json')).write_text(json.dumps(rows,indent=2)+'\n')
full=[r['module'] for r in allrows['final-sweep-2']];rerun=[r['module'] for r in allrows['final-sweep-3-downstream-of-Primitives']];assert full==read(ev/'logs/final-order-used.txt').decode().splitlines();rank={m:i for i,m in enumerate(full)};violations=[{'module':m,'dependency':d} for m in full for d in graph[m] if d in rank and rank[d]>=rank[m]]
assert not violations
closure_cache={}
def closure(m):
 if m in closure_cache:return closure_cache[m]
 seen={m};todo=[m]
 while todo:
  for d in graph[todo.pop()]:
   if d not in seen:seen.add(d);todo.append(d)
 closure_cache[m]=seen;return seen
primmod=prim.removesuffix('.lean');derived=[m for m in full if primmod in closure(m)];assert rerun==derived and len(derived)==223;carried=[m for m in full if m not in set(rerun)];assert len(carried)==418;carryrows=[]
for m in carried:
 deps=sorted(closure(m));assert primmod not in deps;identities=[]
 for d in deps:
  p=d+'.lean';assert trees['mid'][p]==trees['head'][p];identities.append({'module':d,'source_git_blob':trees['head'][p]['oid']})
 carryrows.append({'module':m,'all_reachable_TCSlib_source_blobs_equal_mid_head':True,'reachable_source_count':len(deps),'source_closure_hash':H(json.dumps(identities,sort_keys=True,separators=(',',':'))),'reachable_source_modules':deps})
assert all(trees['mid'][p]==trees['head'][p] for p in ['lean-toolchain','lake-manifest.json']);effective={r['module']:r for r in allrows['final-sweep-2']};effective.update({r['module']:r for r in allrows['final-sweep-3-downstream-of-Primitives']});assert len(effective)==641
(out/'carried418-source-closures.json').write_text(json.dumps(carryrows,indent=2)+'\n');(out/'head-import-graph.json').write_text(json.dumps(graph,indent=2)+'\n');(out/'git-source-blob-maps.json').write_text(json.dumps({'commits':commits,'trees':trees,'changed_all_paths_mid_head':changed,'batch_blob_objects_hashed':len(objects),'owned11_exact_snapshots':owned,'commands':commands},indent=2)+'\n')
(out/'sweep-summary.json').write_text(json.dumps({'sweeps':summaries,'all864_module_attempts_raw_time_and_claimed_source_tree_reconciled':True,'raw_and_summary_discrepancies':discrepancies,'full641_order_matches_supplied':True,'internal_order_violations':violations,'derived_Primitives_downstream_count':len(derived),'rerun223_order_exact_full_order_filter':True,'carried_count':len(carried),'all418_source_closures_equal':True,'toolchain_manifest_blobs_equal':True,'effective_head_union_modules':len(effective),'effective_head_static_admissions':sum(r['static_admitted_declarations'] for r in effective.values()),'effective_head_raw_sorry_warnings':sum(r['raw_sorry_warnings'] for r in effective.values()),'external_TCSlib_dependencies_of_full_order':sorted({d for m in full for d in graph[m] if d not in rank}),'no_native_execution':'Only offline producer-evidence/source-object reconciliation; no Lean/build/tool execution or source integration.'},indent=2)+'\n')
(out/'verified-payload-evidence-hashes.json').write_text(json.dumps(verified,indent=2)+'\n');print(json.dumps(json.loads((out/'sweep-summary.json').read_text()),indent=2))
