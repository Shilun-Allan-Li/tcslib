from pathlib import Path
import json,re,hashlib,collections
OUT=Path(__file__).resolve().parent;c=json.loads((OUT/'context.json').read_text());WT=Path(c['worktree']);SNAP=Path(c['snapshot']);CORE=Path('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0');TARGET=c['owned_file'].removesuffix('.lean').replace('/','.')
packages=sorted([p for p in (WT/'.lake/packages').iterdir() if p.is_dir()]);source_roots=[WT,CORE/'src/lean',CORE/'src/lean/lake']+packages;libs=[SNAP,CORE/'lib/lean']+[p/'.lake/build/lib/lean' for p in packages]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def header_imports(s):
 k=0;n=len(s);im=[];prelude=False
 while k<n:
  if s[k].isspace():k+=1;continue
  if s.startswith('/-',k):
   d=1;k+=2
   while k<n and d:
    if s.startswith('/-',k):d+=1;k+=2
    elif s.startswith('-/',k):d-=1;k+=2
    else:k+=1
   assert d==0
   continue
  if s.startswith('--',k):
   e=s.find('\n',k);k=n if e<0 else e;continue
  e=s.find('\n',k);e=n if e<0 else e;line=s[k:e].strip()
  if line=='prelude':prelude=True;k=e;continue
  if line=='module':k=e;continue
  m=re.match(r'^(?:(?:public|meta)\s+)*import\s+(.+)$',line)
  if m:
   vals=m.group(1).split('--',1)[0].split();im.extend(x for x in vals if x!='all');k=e;continue
  break
 return im,prelude
def source_path(m):
 rel=m.replace('.','/')+'.lean'
 return next((root/rel for root in source_roots if (root/rel).is_file()),None)
def olean_path(m):
 rel=m.replace('.','/')+'.olean'
 return next((root/rel for root in libs if (root/rel).is_file()),None)
cache={};pins={}
def imports(m,override):
 if m==TARGET:return header_imports(override)
 if m not in cache:
  p=source_path(m)
  if p is None:cache[m]=None
  else:cache[m]=header_imports(p.read_text());pins[m]={'source':str(p),'source_sha256':sha(p)}
 return cache[m]
def closure(raw,full):
 seen=set();missing=set();edges={};todo=[TARGET]
 while todo:
  m=todo.pop()
  if m in seen:continue
  seen.add(m);result=imports(m,raw)
  if result is None:missing.add(m);edges[m]=[];continue
  direct,prelude=result
  if full and not prelude and m!='Init':direct=list(dict.fromkeys(direct+['Init']))
  edges[m]=direct
  todo.extend(x for x in direct if full or x.startswith('TCSlib.'))
 return seen,edges,missing
before=(OUT/'Hardness-before.lean.txt').read_text();after=(OUT/'Hardness-after.lean.txt').read_text()
b,be,bmiss=closure(before,False);a,ae,amiss=closure(after,False);assert not bmiss and not amiss
assert set(header_imports(after)[0])-set(header_imports(before)[0])=={'TCSlib.Complexity.ClassNP.PolyTimePrefix'}
assert header_imports(after)[0]==['TCSlib.Complexity.ClassNP.PolyTimePrefix']+header_imports(before)[0]
assert not b-a
added=sorted(a-b);all_tcs_pins={}
for m in sorted(a):
 p=WT/(m.replace('.','/')+'.lean');o=olean_path(m);assert p.is_file() and o is not None,m
 all_tcs_pins[m]={'source':str(p),'source_sha256':sha(p),'olean':str(o),'olean_sha256':sha(o),'newly_imported':m in added}
# Deterministic dependency order and cycle check on complete TCSlib source closure.
def topo(nodes,edges):
 left={n:sum(x in nodes for x in edges[n]) for n in nodes};rev=collections.defaultdict(set)
 for n in nodes:
  for i in edges[n]:rev[i].add(n)
 ready=sorted(n for n in nodes if not left[n]);order=[]
 while ready:
  n=ready.pop(0);order.append(n)
  for d in sorted(rev[n]):
   if d in left:
    left[d]-=1
    if not left[d]:ready.append(d);ready.sort()
 assert len(order)==len(nodes),'cycle detected'
 return order
order=topo(a,ae);external_before=sorted({i for n in b for i in be[n] if not i.startswith('TCSlib.')});external_after=sorted({i for n in a for i in ae[n] if not i.startswith('TCSlib.')})
fb,fbe,fmissingb=closure(before,True);fa,fae,fmissinga=closure(after,True);fulladded=sorted(fa-fb);availability={m:str(olean_path(m)) if olean_path(m) else None for m in sorted(fa)}
missingoleans=sorted(m for m,p in availability.items() if p is None)
result={'status':'Exact source-header import graph crosscheck, no native/cache/Git mutation','target':TARGET,'single_direct_import_added':'TCSlib.Complexity.ClassNP.PolyTimePrefix','all_other_direct_imports_literal_order_preserved':True,'TCSlib_before_count':len(b),'TCSlib_after_count':len(a),'TCSlib_added_count':len(added),'TCSlib_added':added,'TCSlib_removed':[],'TCSlib_all_sources_and_snapshot_outputs_present':True,'TCSlib_dependency_order':order,'TCSlib_pins':all_tcs_pins,'external_direct_roots_before':external_before,'external_direct_roots_after':external_after,'external_direct_roots_added':sorted(set(external_after)-set(external_before)),'full_source_import_closure_including_Core_packages':{'before_count':len(fb),'after_count':len(fa),'added_count':len(fulladded),'added':fulladded,'missing_source_before':sorted(fmissingb),'missing_source_after':sorted(fmissinga),'compiled_modules_missing':missingoleans,'compiled_availability':availability,'scope':'Header imports with nested comments, public/meta imports, prelude and implicit Init accounted for; not a compiled environment import-table dump or cache fetch.'}}
assert not missingoleans,missingoleans
(OUT/'import-closure-delta.json').write_text(json.dumps(result,indent=2)+'\n');(OUT/'new-TCSlib-imports.txt').write_text('\n'.join(added)+'\n');(OUT/'new-external-direct-roots.txt').write_text('\n'.join(result['external_direct_roots_added'])+'\n');(OUT/'full-package-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['TCSlib_before_count','TCSlib_after_count','TCSlib_added_count','TCSlib_added','external_direct_roots_added']},indent=2));print('Full source closure',len(fb),'→',len(fa),'added',len(fulladded),'missing source',len(fmissinga),'missing oleans',len(missingoleans))
