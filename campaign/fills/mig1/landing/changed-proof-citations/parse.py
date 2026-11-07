from pathlib import Path
import hashlib,json,re,collections
p=Path(__file__).resolve().parent
raw=p/'All140-v2.out';s=raw.read_text();req=json.loads((p/'source-roots.json').read_text());run=json.loads((p/'All140-v2-run.json').read_text())
assert run['exit']==0 and run['errors']==0
assert hashlib.sha256(raw.read_bytes()).hexdigest()==run['output_sha256']
rootmaps=[line.split('|')[1:] for line in s.splitlines() if line.startswith('ROOTMAP|')]
assert len(rootmaps)==len(req)==140 and len({r[2] for r in rootmaps})==140
assert re.findall(r'^ROOTCOUNT\|(\d+)$',s,re.M)==['140']
sourcekeys={(r['path'][:-5].replace('/','.'),r['name']) for r in req}
assert sourcekeys=={(owner,n) for owner,n,_ in rootmaps}
desc=[line.split('|')[1:] for line in s.splitlines() if line.startswith('DESC|')]
assert len(desc)==len({tuple(x[:2]) for x in desc})
axs=re.findall(r'^PROOFAX\|([^|\n]+)\|([^|\n]+)\|\[([^\]]*)\]',s,re.M)
assert len(axs)==len(desc)==len(re.findall(r'^PROOFAX\|',s,re.M))
assert {(r,n) for r,n,k in desc}=={(r,n) for r,n,a in axs}
axioms=[{'root':r,'name':n,'axioms':sorted(x.strip() for x in a.split(',') if x.strip())} for r,n,a in axs]
std={'propext','Classical.choice','Quot.sound'}
assert all(set(x['axioms'])<=std for x in axioms)
cites=[]
for line in s.splitlines():
 if not line.startswith('CITED|'):continue
 vals=line.split('|');assert len(vals)==7,line
 _,root,n,part,c,owner,kind=vals;assert part in {'type','value'}
 cites.append({'root':root,'constant':n,'part':part,'reference':c,'owner':owner,'kind':kind})
mods=sorted({x['owner'] for x in cites});files=[x.replace('.','/')+'.lean' for x in mods]
review=p.parent/'review-final-source';prior=(review/'screen-population-final-review.txt').read_text().splitlines();union=sorted(set(files)|set(prior));extra=sorted(set(files)-set(prior))
summary={'root_count':len(rootmaps),'source_public':sum(not r['private'] for r in req),'source_private':sum(r['private'] for r in req),'root_plus_descendant_walks':len(desc),'unique_compiled_names':len({n for r,n,k in desc}),'roots_with_no_generated_descendants':sum(sum(r==root for r,n,k in desc)==1 for _,_,root in rootmaps),'axiom_standard_only':True,'direct_TCSlib_citation_entries':len(cites),'direct_citation_modules':len(mods),'direct_citation_files':files,'per_module_citations':dict(sorted(collections.Counter(x['owner'] for x in cites).items())),'population_before_native':len(prior),'union_population_count':len(union),'new_population_files_from_native':extra,'scope':'Exact changed/new source roots plus all compiled descendants; direct reference edges, not recursive traversal of unchanged imported helper implementations. Native final2 preflight, not full replay; includes acknowledged opaque legacy dependencies.'}
for name,data in [('root-map.json',rootmaps),('axioms.json',axioms),('citations.json',cites),('summary.json',summary)]: (p/name).write_text(json.dumps(data,indent=2)+'\n')
(p/'direct-citation-population.txt').write_text('\n'.join(files)+'\n');(p/'screen-population-union.txt').write_text('\n'.join(union)+'\n')
print(json.dumps(summary,indent=2))
