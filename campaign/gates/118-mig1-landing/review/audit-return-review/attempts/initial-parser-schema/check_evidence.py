import pathlib,json,subprocess,hashlib,re,gzip,collections,base64,zipfile,datetime
R=pathlib.Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
O=pathlib.Path(__file__).parent
G=R/'campaign/gates/118-mig1-landing'
L=R/'campaign/fills/mig1/landing'
SRC='55df52da9754f04b0c71646df29f83f33ec3aa52'; REC='331e68b99c4287232394920e74eed222151f7280'; XCH='15dde3b91c9e6cbfefba6e11ea44545a42125068'
OLD='eaecd6b2afd992ead0844fa5f351eaf143fd1d1c'; BASE='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c'; CAMP='df4341236e04a861e65e29d58b35a713f14c819c'; SCREENBASE='e8196b1020b6be7c1b0894ecd92d8352f951dbb9'
def sha(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(pathlib.Path(p).read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def blob(rev,p):return git('show',rev+':'+str(p))
def save(p,d): (O/p).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
checks={}; problems=[]
def ck(name,v):
 if not v:problems.append(name)
 return v
checks['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
checks['read_only_Git_HEAD']=git('rev-parse','HEAD').decode().strip()
checks['execution_limits']='Own read-only Python3 -I integrity/source/log checks; no supplied code executed; no Lean, screen, lint, replay or actual cached .olean inspection.'
for rev in [SRC,REC,XCH,OLD,BASE,CAMP,SCREENBASE]:
 ck('commit '+rev,git('rev-parse','--verify',rev+'^{commit}').decode().strip()==rev)
 git('cat-file','-e',rev+'^{commit}')
report=(G/'findings.md').read_bytes(); report_rows=re.findall(rb'^\| 118-(\d\d) \| ([^|]+) \|',report,re.M)
checks['report']={'bytes':len(report),'sha256':sha(report),'rows':[(x.decode(),y.decode().strip()) for x,y in report_rows],'verdict':report.decode().split('Verdict:')[-1].strip(),'untracked_at_receipt':j(G/'findings-receipt.json')['tracked_at_receipt']==False}
ck('report receipt',len(report)==12963 and sha(report)=='de242e022ea4aa5f0a0bc2e9690a6bbc83e6a2168dd2cc53a8c9908607c32731' and len(report_rows)==18 and all(y.strip()==b'note' for _,y in report_rows))
pub=j(G/'publication.json');disp=j(G/'dispatch.json');prompt=(G/'prompt.md').read_bytes();pack=(G/'pack.md').read_bytes()
checks['canonical']={'source':SRC,'records':REC,'exchange':XCH,'prompt_sha256':sha(prompt),'pack_sha256':sha(pack),'pack_equals_issued_records':blob(REC,'campaign/gates/118-mig1-landing/pack.md')==pack,'publication_chronology_historical':pub['dispatched']==False,'dispatch_confirmation':disp['dispatch_confirmation']}
ck('pins',all(d['source']==SRC and d['records']==REC and d['exchange']==XCH for d in [pub,disp]))
ck('prompt',sha(prompt)==pub['prompt_sha256']==disp['prompt_sha256'])
ck('pack issued',checks['canonical']['pack_equals_issued_records'])
# Frozen evidence: current nine folders, exactly 1,156 indexed payload entries.
manifest_paths=[L/'replay-post234-final/MANIFEST.json',L/'post234-source-QA-final/MANIFEST.json',L/'post234-source-screen/MANIFEST.json',L/'post234-native3/MANIFEST.json',L/'post234-consumer-seals/MANIFEST.json',L/'post234-core-reader-repair/MANIFEST.json',L/'post234-compiled-accounting/head-current/MANIFEST.json',L/'post234-compiled-accounting/baseline-current/BASELINE-MANIFEST.json',L/'replay-post-f6-tail/MANIFEST.json']
mchecks=[]
for mf in manifest_paths:
 d=j(mf);entries=d if isinstance(d,list) else d['files']; bad=[]
 for e in entries:
  f=mf.parent/e['path']; b=f.read_bytes()
  if len(b)!=e['bytes'] or sha(b)!=e['sha256']:bad.append(e['path'])
 row={'path':str(mf.relative_to(R)),'sha256':sha(mf.read_bytes()),'entries':len(entries),'mismatches':bad}
 mchecks.append(row);ck('manifest '+str(mf),not bad)
checks['frozen_manifests']=mchecks;checks['frozen_entries']=sum(x['entries'] for x in mchecks);ck('1156 manifests',checks['frozen_entries']==1156)
# All source captures independently checked against actual Git, including two 25-file endpoints.
qa=L/'post234-source-QA-final'; inventory=j(qa/'source-inventory-current-full.json'); owners=list(inventory['head'])
source_checks=[]
for side,rev in [('base',SCREENBASE),('head',OLD)]:
 for p in owners:
  f=qa/'inputs'/side/(p+'.txt');equal=f.read_bytes()==blob(rev,p)
  source_checks.append({'side':side,'path':p,'exact_Git':equal,'sha256':sha(f.read_bytes())});ck('source capture '+side+p,equal)
checks['owner_source_captures']=source_checks
checks['source_diff_current']=git('diff','--name-only',CAMP,SRC,'--','*.lean').decode().splitlines()
ck('current twelve file delta',sorted(checks['source_diff_current'])==sorted(owners))
checks['only_later_Lean']=git('diff','--name-only',OLD,SRC,'--','*.lean').decode().splitlines();ck('only Hierarchy later',checks['only_later_Lean']==['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'])
# Count declarations with a fresh nested-comment/string-aware lexical pass; no repository scanner imported.
def stripped(s):
 out=[];i=0;dep=0;line=False;string=False
 while i<len(s):
  c=s[i];n=s[i:i+2]
  if line:
   if c=='\n':line=False;out.append(c)
   else:out.append(' ')
   i+=1;continue
  if dep:
   if n=='/-':dep+=1;out.extend('  ');i+=2
   elif n=='-/':dep-=1;out.extend('  ');i+=2
   else:out.append('\n' if c=='\n' else ' ');i+=1
   continue
  if string:
   out.append(c)
   if c=='\\' and i+1<len(s):out.append(s[i+1]);i+=2;continue
   if c=='"':string=False
   i+=1;continue
  if n=='--':line=True;out.extend('  ');i+=2;continue
  if n=='/-':dep=1;out.extend('  ');i+=2;continue
  if c=='"':string=True
  out.append(c);i+=1
 return ''.join(out)
pattern=re.compile(r'(?m)^[ \t]*(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)?(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class)\b')
census={}
for side in ['base','head']:
 n=collections.Counter();by=[]
 for p in owners:
  code=stripped((qa/'inputs'/side/(p+'.txt')).read_text()); matches=list(pattern.finditer(code));counts=collections.Counter('private' if 'private' in (m['mods'] or '').split() else 'public' for m in matches)
  expected=collections.Counter('private' if d['private'] else 'public' for d in inventory[side][p]);ck('lexical count '+side+p,counts==expected)
  n.update(counts);by.append({'path':p,'public':counts['public'],'private':counts['private'],'inventory_agrees':counts==expected})
 census[side]={'totals':dict(n),'by_file':by}
checks['independent_source_census']=census;ck('source counts',census['base']['totals']=={'public':386,'private':1080} and census['head']['totals']=={'public':383,'private':766})
# Independently compare source inventory fields (full headers/homes/privacy/kinds/order) whose captures are Git-bound.
def invrows(side):return {(p,d['name']):d for p,v in inventory[side].items() for d in v}
binv=invrows('base');hinv=invrows('head');bpub={k:v for k,v in binv.items() if not v['private']};hpub={k:v for k,v in hinv.items() if not v['private']}
checks['public_added']=[{'path':p,'name':n} for p,n in sorted(hpub.keys()-bpub.keys())]
checks['public_removed']=[{'path':p,'name':n} for p,n in sorted(bpub.keys()-hpub.keys())]
header_changes=[{'path':p,'name':n} for p,n in binv.keys()&hinv.keys() if any(binv[p,n][k]!=hinv[p,n][k] for k in ['header','kind','private'])]
checks['header_changes']=sorted(header_changes,key=lambda d:(d['path'],d['name']))
checks['shared_public_headers_exact']=all(bpub[k]['header']==hpub[k]['header'] and bpub[k]['kind']==hpub[k]['kind'] for k in bpub.keys()&hpub.keys())
ck('shared public headers',checks['shared_public_headers_exact']);ck('five private exceptions',len(header_changes)==5 and all(binv[d['path'],d['name']]['private'] for d in header_changes))
checks['private_header_names']=[x['name'] for x in checks['header_changes']]
# Exact endpoint and import-context reuse, independently reconstructed from Git source imports.
ss=j(L/'post234-source-screen/summary.json');pop=ss['actual_runs']['head']['command'][7:]
# command includes script, root, then the25 files. Select only TCSlib entries, avoid relying on offsets.
pop=[x for x in ss['actual_runs']['head']['command'] if x.startswith('TCSlib/') and x.endswith('.lean')]
checks['screen_endpoints']=[{'path':p,'BASE_exact':blob(SCREENBASE,p)==blob(CAMP,p),'HEAD_exact':blob(OLD,p)==blob(SRC,p)} for p in pop]
ck('50 endpoints',len(pop)==25 and all(d['BASE_exact'] and d['HEAD_exact'] for d in checks['screen_endpoints']))
def lsblobs(rev):
 d={}
 for line in git('ls-tree','-r',rev,'--','TCSlib').decode().splitlines():
  meta,p=line.split('\t',1)
  if p.endswith('.lean'):d[p[:-5].replace('/','.')]=meta.split()[2]
 return d
def imports(rev):
 d={}
 for ln in git('grep','-n','-e','^import ',rev,'--','TCSlib').decode().splitlines():
  _,p,no,text=ln.split(':',3)
  if p.endswith('.lean'):d.setdefault(p[:-5].replace('/','.'),[]).extend(text[7:].split())
 return d
def closure(start,imp):
 seen=set();todo=list(start)
 while todo:
  x=todo.pop()
  if x in seen:continue
  seen.add(x);todo.extend(y for y in imp.get(x,[]) if y.startswith('TCSlib.'))
 return seen
modules=[p[:-5].replace('/','.') for p in owners]+['TCSlib.Complexity.TuringMachine.Finite']
ctx=[]
for old,new in [(BASE,CAMP),(OLD,SRC)]:
 ia,ib=imports(old),imports(new);cl_a=closure(modules,ia);cl_b=closure(modules,ib);a,b=lsblobs(old),lsblobs(new)
 row={'old':old,'new':new,'closure_size_old':len(cl_a),'closure_size_new':len(cl_b),'same_module_set':cl_a==cl_b,'all_module_blobs_equal':cl_a==cl_b and all(a[x]==b[x] for x in cl_a),'Hierarchy_reachable':any(x.endswith('.Hierarchy') for x in cl_b)}
 ctx.append(row);ck('import reuse '+new,row['same_module_set'] and row['all_module_blobs_equal'] and not row['Hierarchy_reachable'])
checks['import_context_reuse']=ctx
save('source-and-identity-checks.json',checks)
print(json.dumps({'stage':'source/identity/manifests','frozen_entries':checks['frozen_entries'],'source_counts':{k:v['totals'] for k,v in census.items()},'contexts':ctx,'problems':problems},indent=2))
# Raw census/axioms/type hashes independently parsed; do not evaluate any enclosed code or Lean.
raw={};censusdata={};axdata={}
for side,p in [('Base',L/'post234-compiled-accounting/baseline-current/Base.out.gz'),('Head',L/'post234-compiled-accounting/head-current/Head-inventory.out.gz')]:
 c={};a={};u={};h=hashlib.sha256();size=0;tags=collections.Counter()
 with gzip.open(p,'rb') as f:
  for line in f:
   h.update(line);size+=len(line)
   if b'|' not in line:continue
   t,payload=line.split(b'|',1)
   if t not in [b'CENSUS',b'ALLAX',b'PUBLICAX']:continue
   d=json.loads(payload);tags[t.decode()]+=1
   target={b'CENSUS':c,b'ALLAX':a,b'PUBLICAX':u}[t]
   ck(side+' duplicate '+d['name'],d['name'] not in target);target[d['name']]=d
 ck(side+' exact AX coverage',c.keys()==a.keys() and set(u)=={n for n,d in c.items() if not d['private']})
 primary={n:d for n,d in c.items() if d['owner']!='TCSlib.Complexity.TuringMachine.Finite'};finite={n:d for n,d in c.items() if d['owner']=='TCSlib.Complexity.TuringMachine.Finite'}
 for n,d in c.items():d['type_hash']=sha(d['typeExpr'].encode())
 nonstd={n:d['axioms'] for n,d in a.items() if not set(d['axioms'])<= {'propext','Classical.choice','Quot.sound'}}
 raw[side]={'raw_bytes':size,'raw_sha256':h.hexdigest(),'tags':dict(tags),'primary':len(primary),'primary_private':sum(d['private'] for d in primary.values()),'Finite':len(finite),'nonstandard':nonstd,'gzip_Base64_exact':base64.b64decode((p.parent/(p.name+'.base64.txt')).read_bytes())==p.read_bytes()}
 censusdata[side]=c;axdata[side]=a
b,h=censusdata['Base'],censusdata['Head'];shared=b.keys()&h.keys();raw['combined_delta']={'added':len(h.keys()-b.keys()),'removed':len(b.keys()-h.keys()),'shared':len(shared),'shared_primary':sum(h[n]['owner']!='TCSlib.Complexity.TuringMachine.Finite' for n in shared)}
raw['rawtype_differences']=sorted(n for n in shared if b[n]['typeExpr']!=h[n]['typeExpr'])
raw['owner_changes']=[n for n in shared if b[n]['owner']!=h[n]['owner']]
raw['Finite_exact']=all(b[n]==h[n] and axdata['Base'][n]==axdata['Head'][n] for n in shared if h[n]['owner']=='TCSlib.Complexity.TuringMachine.Finite')
selected=j(L/'post234-compiled-accounting/head-current/current154-selected-AX.json');sel=selected['all_selected_constants'];raw['selected']={'roots':selected['conservative_selected_roots'],'actual_changed_roots':selected['actual_changed_roots'],'descendants':selected['descendants_additional'],'constants':len(sel),'distribution':dict(collections.Counter(','.join(v['axioms']) for v in sel.values())),'all_standard_or_subset':all(set(v['axioms'])<= {'propext','Classical.choice','Quot.sound'} for v in sel.values()),'all_raw_AX_agree':all(v['axioms']==axdata['Head'][n]['axioms'] for n,v in sel.items())}
ck('raw counts',raw['Base']['primary']==5701 and raw['Head']['primary']==4416 and raw['Base']['Finite']==59 and raw['Head']['Finite']==59)
ck('raw delta',raw['combined_delta']=={'added':399,'removed':1684,'shared':4076,'shared_primary':4017})
ck('raw94',len(raw['rawtype_differences'])==94);ck('finite exact',raw['Finite_exact']);ck('selected388',len(sel)==388 and raw['selected']['all_standard_or_subset'] and raw['selected']['all_raw_AX_agree'])
raw['problems']=list(problems);save('raw-accounting-checks.json',raw)
print(json.dumps({'stage':'raw accounting','Base':{k:v for k,v in raw['Base'].items() if k!='nonstandard'},'Head':raw['Head'],'delta':raw['combined_delta'],'type_differences':len(raw['rawtype_differences']),'selected':raw['selected'],'problems':problems},indent=2))
# Whole-map replay lineage and recorded source/log identities, independent of receipt summary.
nat=j(L/'post234-native3/snapshot-objects.json');m3=j(L/'replay-post234-final/snapshot-objects.json');m4=j(L/'replay-post-f6-tail/snapshot-objects.json');nr=j(L/'post234-native3/receipt.json')
lineage={'map_sizes':[len(nat['input']),len(nat['output']),len(m3['input_MAC5']),len(m3['output_MMIG3']),len(m4['input']),len(m4['output'])],'native_MAC5_equals_MMIG3_MAC5':nat['input']==m3['input_MAC5'],'MMIG4_input_equals_whole_MMIG3_output':m4['input']==m3['output_MMIG3'],'owner_output_mismatches':[p for p in nat['changed'] if nat['output'][p]!=m3['output_MMIG3'][p]],'MMIG3_changed':[p for p,v in m3['input_MAC5'].items() if v!=m3['output_MMIG3'][p]],'MMIG4_changed':[p for p,v in m4['input'].items() if v!=m4['output'][p]],'native_rows':[],'replays':[]}
for row in nr['rows']:
 data=(L/'post234-native3'/row['log']).read_bytes();p=row['file']
 lineage['native_rows'].append({'file':p,'log_exact':sha(data)==row['sha256'] and len(data)==row['bytes'],'source_exact':sha(blob(SRC,p))==row['source_sha256'],'exit':row['exit'],'errors':row['errors'],'sorries':row['sorries']})
for name,folder,count,total in [('MMIG3','replay-post234-final',394,60),('MMIG4','replay-post-f6-tail',2,0)]:
 slug=name.lower();fold=L/folder;log=(fold/('replay-'+slug+'.log')).read_text();rows=re.findall(r'^([^ \n]+) exit=(\d+) errors=(\d+) sorry=(\d+)$',log,re.M);order=(fold/('order-'+slug+'.txt')).read_text().splitlines();launch=(fold/('replay-'+slug+'-launches.log')).read_text().splitlines();static=(fold/('replay-'+slug+'-static.txt')).read_text()
 r={'name':name,'rows':len(rows),'all_pass':all(e=='0' and er=='0' for _,e,er,_ in rows),'module_order_exact':[p for p,*_ in rows]==order,'launch_rows':len(launch),'all_launch_j4':all('-j4' in s for s in launch),'static_summary':static.splitlines()[-3:]};lineage['replays'].append(r)
 ck(name+' row/order/launch',r['rows']==count and r['all_pass'] and r['module_order_exact'] and r['launch_rows']==count and r['all_launch_j4'])
ck('lineage',lineage['native_MAC5_equals_MMIG3_MAC5'] and lineage['MMIG4_input_equals_whole_MMIG3_output'] and not lineage['owner_output_mismatches'] and len(lineage['MMIG3_changed'])==118 and lineage['MMIG4_changed']==['TCSlib/Complexity/SpaceComplexity/Hierarchy.olean'])
ck('native rows',len(lineage['native_rows'])==12 and all(r['log_exact'] and r['source_exact'] and r['exit']==r['errors']==0 for r in lineage['native_rows']) and sum(r['sorries'] for r in lineage['native_rows'])==3)
lineage['problems']=list(problems);save('native-replay-map-checks.json',lineage);print(json.dumps({'stage':'native/replay lineage','map_sizes':lineage['map_sizes'],'owner_mismatches':lineage['owner_output_mismatches'],'replays':lineage['replays'],'problems':problems},indent=2))
save('CHECK-SUMMARY.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'problems':problems,'PASS':not problems,'claims':'Read-only checks only; independent Lean execution absent.'})
