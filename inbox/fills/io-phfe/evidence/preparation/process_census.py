"""Validate completed native inventories and export delivery tables; starts no Lean."""
from pathlib import Path
import csv,json,re,sys,hashlib
root=Path.cwd();ev=Path(sys.argv[1]);runs=[Path(x) for x in sys.argv[2:]];run=runs[-1];dest=Path('evidence/statements');dest.mkdir(exist_ok=True)
collect=(ev/'collector-run/mods/.lake_io-phfe-rule10_Collect.log').read_text()
def rows(prefix,src):return [json.loads(l[len(prefix):]) for l in src.splitlines() if l.startswith(prefix)]
roots=rows('ROOT ',collect);expected={r['name']['display'] for r in roots};assert len(expected)==len(roots)
ordered=sorted(expected);position={n:i for i,n in enumerate(ordered)}
merged={key:{} for key in ['PHFE_STMT ','PHFE_AXIOMS ','PHFE_SORRY_TRACE ']};chunkmap={};printed=set();runmeta=[];alllogs=[]
for index,run in enumerate(runs):
 logpath=run/'mods/.lake_io-phfe-rule10_Census.log'
 if not logpath.exists():logpath=run/'mods/.lake_io-phfe-rule10_CensusRepair.log'
 text=logpath.read_text();alllogs.append(text)
 results=[json.loads(l) for l in (run/'results.jsonl').read_text().splitlines()];checks=[r for r in results if 'module' in r];assert len(checks)==1
 r=checks[0];errors=[l for l in text.splitlines() if re.match(r'^\S+\.lean:\d+:\d+: error[:(]',l)]
 if r['rc'] or r['errors']:
  assert index<len(runs)-1 and r['rc']==1 and errors and all('sorryAx dependency had no path:' in e for e in errors),'unresolved probe failure'
 else:assert not errors
 complete=rows('PHFE_CENSUS_CHUNK ',text);starts={c['start'] for c in complete}
 for c in complete:
  if c['start'] in chunkmap:assert chunkmap[c['start']]==c
  chunkmap[c['start']]=c
 valid=lambda n:(position[n]//50)*50 in starts
 for prefix in merged:
  for obj in rows(prefix,text):
   assert obj['name'] in expected
   if not valid(obj['name']):continue
   prior=merged[prefix].get(obj['name'])
   if prior is not None and prefix!='PHFE_SORRY_TRACE ':assert prior==obj
   merged[prefix][obj['name']]=obj
 for line in text.splitlines():
  m=re.match(r"^'(.+)' (?:depends on axioms|does not depend on any axioms)",line)
  if m and m[1] in expected and valid(m[1]):printed.add(m[1])
 runmeta.append({'run':str(run),'rc':r['rc'],'errors':r['errors'],'complete_chunks_retained':len(complete),'log_sha256':hashlib.sha256(text.encode()).hexdigest()})
log=''.join(alllogs);stmts=list(merged['PHFE_STMT '].values());axs=list(merged['PHFE_AXIOMS '].values());traces=list(merged['PHFE_SORRY_TRACE '].values());chunks=list(chunkmap.values())
for what,rs in [('statements',stmts),('axioms',axs)]:assert len(rs)==len({r['name'] for r in rs}) and {r['name'] for r in rs}==expected,what
assert sum(r['count'] for r in chunks)==len(expected) and sorted(chunkmap)==list(range(0,len(expected),50))
assert not any('⋯' in r['type'] for r in stmts),'truncated type'
assert printed==expected,('incomplete #print axioms records',len(printed),len(expected))
std={'propext','Classical.choice','Quot.sound'};byax={r['name']:r for r in axs}
assert all(set(r['nonstandard'])==set(r['axioms'])-std for r in axs)
other=[r for r in axs if set(r['axioms'])-std-{'sorryAx'}];assert not other,other
admitted={r['name'] for r in axs if 'sorryAx' in r['axioms']};assert admitted=={r['name'] for r in traces}
assert all(r['path'][0]==r['name'] and r['path'][-1]=='sorryAx' for r in traces)
for filename,rs in [('StmtDump.jsonl',stmts),('axioms.jsonl',axs),('sorry-traces.jsonl',traces)]:
 (dest/filename).write_text(''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in rs))
snap=json.loads((ev/'snapshot.json').read_text());decls=json.loads((ev/'declarations-text.json').read_text())['rows'];coverage=json.loads((ev/'controls-coverage.json').read_text());readers={r['name']:r['reader'] for r in coverage['rows'] if r['requested_pair']}
readerlog=(ev/'collector-run/mods/.lake_io-phfe-rule10_ReaderCatalog.log').read_text();verified=rows('PHFE_READER ',readerlog);assert len(verified)==387 and all(r['ok'] for r in verified)
written={r['name']:r for r in decls};native=[]
for r in roots:
 name=r['name']['display'];module=r['module'];file=module.replace('.','/')+'.lean'
 candidates=[d for d in decls if d['module']==module and (d['name']==name or name.endswith('.'+d['name']))]
 role='written';d=candidates[0] if len(candidates)==1 else None
 if d is None:
  candidates=[d for d in decls if d['module']==module and (name.startswith(d['name']+'.') or (d['private'] and ('.'+d['name']+'.') in name))]
  d=max(candidates,key=lambda x:len(x['name'])) if candidates else None;role='generated'
 line=d['line'] if d else None;tag='generated support; see owning declaration/module'
 if d:
  text=Path(file).read_text();prefix='\n'.join(text.splitlines()[:line-1]);start=prefix.rfind('/--');end=prefix.rfind('-/')
  if start>=0 and end>start:
   doc=prefix[start:end];tags=re.findall(r'\[(?:GJLS21|Wee20|AGW20|IW14|JLS26)[^\]]*\]',doc);tag='; '.join(tags) if tags else 'technical glue; module references'
 native.append({'name':name,'module':module,'kind':r['kind'],'file':file,'line':line,'role':role,'source_tag':tag,'reader':readers.get(d['name'],'') if d else '', 'axioms':','.join(byax[name]['axioms'])})
with (dest/'native-declarations.tsv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(native[0]),delimiter='\t');w.writeheader();w.writerows(native)
with (dest/'written-declarations.tsv').open('w') as f:
 fields=['name','path','line','kind','private','reader'];w=csv.DictWriter(f,fieldnames=fields,delimiter='\t');w.writeheader()
 for d in decls:w.writerow({k:(readers.get(d['name'],'') if k=='reader' else d.get(k,'')) for k in fields})
summary={'source_head':snap['head_at_snapshot'],'native_stored_constants':len(expected),'written_declarations':len(decls),'full_types_without_elisions':len(stmts),'print_axioms_records':len(expected),'standard_axiom_only':len(expected)-len(admitted),'sorryAx_dependent':len(admitted),'other_nonstandard_axioms':len(other),'native_readers_requested':len(verified),'native_readers_verified':len(verified),'source_snapshot_sha256':hashlib.sha256((ev/'snapshot.json').read_bytes()).hexdigest(),'census_log_sha256':hashlib.sha256(log.encode()).hexdigest(),'native_runs':runmeta,'complete_native_chunks':len(chunks),'aggregation':'Only completed zero-error chunk commands retained; failed chunks replaced by clean replay; raw failures preserved'}
(dest/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
