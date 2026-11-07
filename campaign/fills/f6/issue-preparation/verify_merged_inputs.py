"""Read-only merged-base verification; no retained/delivered generator is executed."""
from pathlib import Path
import collections,datetime,hashlib,json,os,re,subprocess
out=Path(__file__).resolve().parent;root=out.parents[3];wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-camp');base='3023dc1408c3d216fc07a7cbba9ae30135b861ed';api='1160c18f03fd318f0dec25738790935fa61379d4';old=root/'campaign/fills/f6/drafts/packet-preparation';env=dict(os.environ,GIT_OPTIONAL_LOCKS='0');H=lambda b:hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.run(['git','-C',str(wt),*a],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,env=env).stdout
assert git('rev-parse','HEAD').decode().strip()==base
for c in [base,api]:assert git('cat-file','-t',c).strip()==b'commit'
assert not git('diff','--name-only',api,base,'--','*.lean').strip()
# Preserve positions while masking nested comments; strings do not affect import headers.
def clean(s):
 o=list(s);i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;o[i:i+2]='  ';i+=2
   elif s.startswith('-/',i):depth-=1;o[i:i+2]='  ';i+=2
   else:
    if s[i]!='\n':o[i]=' '
    i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:i+=1
  elif s.startswith('/-',i):depth=1;o[i:i+2]='  ';i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;o[i:j]=' '*(j-i);i=j
  elif s[i]=='"':string=True;i+=1
  else:i+=1
 return ''.join(o)
def imports(s):
 result=[]
 for l in clean(s).splitlines():
  l=l.strip()
  if not l:continue
  if l=='prelude':continue
  if l.startswith('import '):result.extend(l[7:].split());continue
  break
 return result
entries={}
for line in git('ls-tree','-r',base).decode().splitlines():
 meta,path=line.split('\t',1);mode,kind,blob=meta.split()
 if path.endswith('.lean') and (path.startswith('TCSlib/') or path=='TCSlib.lean'):entries[path]=(kind,blob)
texts={};mods={}
for p,(kind,blob) in entries.items():
 b=(wt/p).read_bytes();assert kind=='blob' and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob;texts[p]=b;mods[p[:-5].replace('/','.')]=imports(b.decode())
def topo(roots):
 done=set();active=set();order=[]
 def visit(m):
  if m in done:return
  assert m not in active;active.add(m)
  for i in sorted(mods[m]):
   if i.startswith('TCSlib'):assert i in mods;visit(i)
  active.remove(m);done.add(m);order.append(m)
 for m in sorted(roots):visit(m)
 return order
owned='TCSlib.Complexity.SpaceComplexity.Hierarchy';reverse={}
for m,imps in mods.items():
 for i in imps:reverse.setdefault(i,set()).add(m)
down=set();todo=[owned]
while todo:
 m=todo.pop()
 if m in down:continue
 down.add(m);todo.extend(reverse.get(m,()))
down.discard('TCSlib');boot=topo([owned]);final=topo(down);downorder=[m for m in final if m in down]
assert (len(boot),len(downorder),len(final))==(132,2,229)
assert 'TCSlib' not in boot and 'TCSlib' not in final
orders={'bootstrap-order.txt':boot,'downstream-order.txt':downorder,'final-order.txt':final}
for name,ms in orders.items():
 data=''.join(m.replace('.','/')+'\n' for m in ms).encode();assert data==(old/name).read_bytes();(out/'inputs'/name).write_bytes(data)
math=sorted({i for m in final for i in mods[m] if i.startswith('Mathlib.')});assert len(math)==65
external=sorted({i for m in final for i in mods[m] if not i.startswith('TCSlib')})
for n,rows in [('mathlib-roots.txt',math),('external-imports.txt',external)]:
 b=('\n'.join(rows)+'\n').encode();assert b==(old/n).read_bytes();(out/'inputs'/n).write_bytes(b)
source=[]
for m in final:
 p=m.replace('.','/')+'.lean';source.append({'path':p,'git_blob':entries[p][1],'sha256':H(texts[p]),'imports':mods[m]})
assert source==json.loads((old/'source-inputs.json').read_text());(out/'inputs/source-inputs.json').write_bytes((old/'source-inputs.json').read_bytes())
# Independent static source-token census, preserving the prior display format.
DECL=re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable)\s+)*)(theorem|lemma|def|abbrev|instance|example|structure)\s+([A-Za-z0-9_.\u0027₀-₉]+)?',re.M)
admissions=[];display=[]
for m in final:
 p=m.replace('.','/')+'.lean';s=clean(texts[p].decode());matches=list(DECL.finditer(s));names=[]
 for i,d in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else len(s);part=s[d.start():end]
  if re.search(r'\bsorry\b',part):
   name=d.group(3) or '?';private='private' in (d.group(1) or '');names.append(name+(' [private]' if private else ''));admissions.append({'file':p,'declaration':name,'kind':d.group(2),'private':private,'declaration_line':s[:d.start()].count('\n')+1,'sorry_lines':[s[:d.start()+t.start()].count('\n')+1 for t in re.finditer(r'\bsorry\b',part)],'owned_target':p.endswith('/Hierarchy.lean') and name=='space_universal'})
 if names:display.append(f"{p[:-5].replace('TCSlib/Complexity/','')}: {len(names)}: {', '.join(names)}")
display=('\n'.join(display+[f'TOTAL {len(admissions)}'])+'\n').encode();assert display==(old/'base-sorry-static.txt').read_bytes();assert len(admissions)==22 and sum(x['owned_target'] for x in admissions)==1
(out/'inputs/base-sorry-static.txt').write_bytes(display);(out/'inputs/target-admissions.json').write_text(json.dumps({'source':base,'scope':'Static admitted-declaration token census, not native axiom audit','total':22,'owned':1,'inherited_MIG_specifications':17,'inherited_RecordTable_results':4,'declarations':admissions},indent=2)+'\n')
hierarchy=texts['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'];header=(old/'space_universal-header.txt').read_bytes();assert hierarchy.count(header)==1 and hierarchy==(old/'Hierarchy.lean.txt').read_bytes();assert H(header)=='89d2609a76de64f38283e2d9cf7338791aa451a7e08a46fb02f07eb182f5f62f'
for name,data in [('Hierarchy.lean.txt',hierarchy),('space_universal-header.txt',header),('owned-files.txt',(old/'owned-files.txt').read_bytes())]:(out/'inputs'/name).write_bytes(data)
# Verify all source/tool bytes of the executed full21-file provisional baseline.
pop=(root/'campaign/fills/f6/drafts/final-brief-review/provisional-TCSlib-screen.txt').read_bytes();paths=pop.decode().splitlines();assert len(paths)==21
run=json.loads((root/'campaign/fills/f6/drafts/screen-provisional-base/run.json').read_text());assert run['exit']==0 and run['status']=='PASS';checked=[]
for x in run['files']:
 b=texts[x['path']];assert H(b)==x['sha256'] and len(b)==x['bytes'] and entries[x['path']][1]==x['git_blob'];checked.append(dict(x,merged_base_blob_identical=True))
assert [x['path'] for x in checked]==paths and H(pop)==run['population_sha256']
(out/'inputs/screen-population.txt').write_bytes(pop)
mathpop=(root/'campaign/fills/f6/drafts/final-brief-review/v6-supplement/combined-named-Mathlib-comparisons.txt').read_bytes();(out/'inputs/named-Mathlib-comparisons.txt').write_bytes(mathpop)
mathpins=[]
for path in mathpop.decode().splitlines():
 b=(wt/path).read_bytes();dest=out/'inputs'/(path.removeprefix('.lake/packages/mathlib/').replace('/','__')+'.txt');dest.write_bytes(b);mathpins.append({'path':path,'inert_input':str(dest.relative_to(out)),'sha256':H(b),'bytes':len(b)})
toolpaths=['lean-toolchain','lakefile.lean','lake-manifest.json','devtools/seyoon/leanelab.sh','devtools/seyoon/leanelab-o.sh','scripts/lean_check_tree.sh','scripts/copy-text-screen-v3.py'];tools=[]
for p in toolpaths:
 b=(wt/p).read_bytes();assert b==git('show',base+':'+p);assert b==git('show',api+':'+p);assert b==(root/p).read_bytes();dest=out/'inputs'/(p.replace('/','__')+'.txt');dest.write_bytes(b);tools.append({'path':p,'sha256':H(b),'bytes':len(b),'merged_and_API_and_current_records_bytes_identical':True,'inert_input':str(dest.relative_to(out))})
assert next(x['sha256'] for x in tools if x['path']=='scripts/copy-text-screen-v3.py')==run['tool_sha256']
receipt={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'merged_base':base,'API_source_commit':api,'actual_wt_camp_HEAD_verified':True,'full_Lean_git_diff_empty':True,'tracked_Lean_sources_checked_against_actual_Git_blobs':len(entries),'final_source_inputs':229,'source_input_rows_byte_identical_to_provisional':True,'orders':{'bootstrap':132,'downstream':2,'final':229,'Mathlib_direct_roots':65},'six_generator_outputs_byte_identical':True,'source_admitted_declarations':22,'owned_original_targets':1,'inherited_MIG':17,'inherited_RecordTable':4,'Hierarchy_sha256':H(hierarchy),'target_header_sha256':H(header),'screen_baseline':'Prior actual API1160 execution adopted by exact21source+tool+population byte equality, not rerun or fresh semantic clearance','screen_files':checked,'tool_inputs':tools,'named_Mathlib_inputs':mathpins,'no_Lean_screen_cache_source_or_Git_mutation':True,'records_commit_bundle_sha_section_count':'UNISSUED; root finalizes after records commit'}
(out/'merged-input-verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ['screen_files','tool_inputs','named_Mathlib_inputs']},indent=2))
