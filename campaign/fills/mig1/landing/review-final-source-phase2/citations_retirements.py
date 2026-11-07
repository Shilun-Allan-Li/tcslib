"""Source-only citation ownership and exact retired-name enumeration. No Lean/screens."""
from pathlib import Path
import sys,importlib.util,contextlib,io,json,re,os,collections,hashlib
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4];wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad'
spec=importlib.util.spec_from_file_location('r',out/'source_review.py');R=importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):spec.loader.exec_module(R)
index=collections.defaultdict(list);texts={};code={};graph={};decl_body={}
for f in sorted((wt/'TCSlib').rglob('*.lean')):
 rel=str(f.relative_to(wt));s=f.read_text();c=R.P.clean(s);texts[rel]=s;code[rel]=c;graph[rel]=[];stack=[]
 for i,line in enumerate(c.splitlines(),1):
  if line.startswith('import '):graph[rel]+=[x.replace('.','/')+'.lean' for x in line.split()[1:] if x.startswith('TCSlib.')]
  m=R.P.DECL.match(line)
  if m and m['name'] and m['name'] not in [':','where']:
   ns='.'.join(n for k,n in stack if k=='ns');n=m['name'];n=n[7:] if n.startswith('_root_.') else (ns+'.'+n if ns else n)
   index[n].append({'name':n,'path':rel,'kind':m['kind'],'private':'private' in m['mods'].split(),'line':i,'origin':'current-source-declaration'})
  elif line.startswith('namespace '):stack.extend(('ns',n) for n in line.split()[1].split('.'))
  elif re.match(r'(?:noncomputable\s+)?section\b',line):stack.append(('section',line.split()[-1] if len(line.split())>1 else ''))
  elif line.startswith('end'):
   words=line.split();end=words[1] if len(words)>1 else ''
   if not end:
    if stack:stack.pop()
   else:
    for part in reversed(end.split('.')):
     while stack and stack[-1][1]!=part:stack.pop()
     if stack:stack.pop()
# Prior compiled owner data is an ownership supplement only; it is not a final proof execution claim.
prior=json.loads((root/'campaign/fills/mig1/landing/preflight-current1/direct-citations.json').read_text())
for row in prior:
 if not row['owner'].startswith('TCSlib.'):continue
 n=row['name'];rel=row['owner'].replace('.','/')+'.lean'
 if n.startswith('_private.'):continue
 if not any(x['path']==rel for x in index[n]):index[n].append({'name':n,'path':rel,'kind':row['kind'],'private':False,'line':None,'origin':'prior-compiled-owner-supplement'})
byshort=collections.defaultdict(list)
for n,rows in index.items():
 for row in rows:
  if not row['private']:byshort[n.rsplit('.',1)[-1]].append(row)
def closure(f):
 seen={f};todo=[f]
 while todo:
  for g in graph.get(todo.pop(),[]):
   if g not in seen:seen.add(g);todo.append(g)
 return seen
closures={f:closure(f) for f in R.FILES}
keywords=set('by exact apply refine intro intros rintro obtain rcases cases case with have let in fun at only using first all_goals constructor next induction simp simpa rw rfl unfold change show from calc if then else match return do true false none some end where repeat try congr funext dsimp omega positivity norm_num ring simp_all simp_rw aesop classical decide fail_if_success assumption subst clear specialize rename_i on_goal done skip qed'.split())
token=re.compile(r"(?<![\w'.])([A-Za-z_\u0370-\u03ff][\w'?!]*(?:\.[A-Za-z_\u0370-\u03ff][\w'?!]*)*)")
citations=[];ambiguous=collections.defaultdict(set);unresolved=collections.Counter();cited=set();owners=set(R.FILES)
def resolve(t,f,ns):
 t=t.removeprefix('_root_.');tries=[t,ns+'.'+t,'Turing.'+t,'Turing.FinTM.'+t,'Complexity.'+t,'WordRAM.'+t]
 for n in dict.fromkeys(tries):
  rows=[x for x in index.get(n,[]) if x['path'] in closures[f] and (not x['private'] or x['path']==f)]
  if rows:return rows,'exact-or-namespace'
 # Existing generated equations belong to the already identified definition's home.
 for suffix in ['.eq_def','.eq_1','.eq_2','.eq_3','.eq_4']:
  if t.endswith(suffix):
   rows,_=resolve(t.removesuffix(suffix),f,ns)
   if rows:return [dict(x,name=x['name']+suffix,origin='generated-equation-home') for x in rows],'generated-equation'
 short=t.rsplit('.',1)[-1]
 rows=[x for x in byshort.get(short,[]) if x['path'] in closures[f]]
 paths={x['path'] for x in rows}
 if len(paths)==1:return rows,'unique-imported-owner-suffix'
 if len(paths)>1:ambiguous[t].update(paths)
 return [],'unresolved'
for row in R.api['proof_roots']:
 d=next(x for x in R.DECLS['current'][row['path']] if x['name']==row['name']);ns=d['name'].rsplit('.',1)[0];seen=set()
 for part,s in [('proof-and-header',d['header_raw']+'\n'+d['body']),('leading-proof-documentation',d['doc'])]:
  s=R.P.clean(s) if part=='proof-and-header' else s
  for m in token.finditer(s):
   t=m[1]
   if t in keywords or len(t)==1:continue
   matches,method=resolve(t,row['path'],ns)
   if not matches:
    if '.' in t and t.split('.')[0] not in {'List','Nat','Int','Fin','Bool','Function','Prod','Option','Set','Finset','Fintype','Classical','Subtype'}:unresolved[t]+=1
    continue
   for hit in matches:
    k=(part,t,hit['name'],hit['path'])
    if k in seen:continue
    seen.add(k);owners.add(hit['path']);cited.add(hit['name']);citations.append({'proof':row['name'],'proof_home':row['path'],'part':part,'token':t,'resolved':hit['name'],'owner':hit['path'],'method':method,'owner_origin':hit['origin']})
# Expand explicit public abbreviations using current defining source and actual owner, without assuming
# a reducible alias's displayed home exposes every ordinary implementation it names.
abbrev=[]
for n in sorted(cited):
 for hit in index.get(n,[]):
  if hit['kind']!='abbrev' or hit['private']:continue
  s=texts[hit['path']];lines=s.splitlines(keepends=True);start=hit['line'] or 1
  tail=''.join(lines[start-1:]);mt=re.search(r'(?m)^(?:private\s+)?(?:def|abbrev|theorem|lemma|instance|structure|inductive)\b',tail.split('\n',1)[1] if '\n' in tail else '')
  block=tail[:len(tail.split('\n',1)[0])+1+mt.start()] if mt else tail[:2500]
  refs=[]
  for tm in token.finditer(R.P.clean(block)):
   rs,_=resolve(tm[1],hit['path'],n.rsplit('.',1)[0])
   for x in rs:
    if x['name']==n:continue
    refs.append({'name':x['name'],'owner':x['path']});owners.add(x['path'])
  abbrev.append({'abbrev':n,'owner':hit['path'],'implementation_references':refs})
# Same-home helpers cited by new proofs are already inside an owned population. Include all prior
# directly compiled foreign homes conservatively even where this lexical pass does not see notation.
compiledHomes={r['owner'].replace('.','/')+'.lean' for r in prior if r['owner'].startswith('TCSlib.')};owners|=compiledHomes
# Retain the complete previously captured25-file conservative union; no capped population.
previous25=set((out.parent/'review-final-source/screen-population-final-review.txt').read_text().splitlines());owners|=previous25
(out/'source-citations.json').write_text(json.dumps({'proof_roots':len(R.api['proof_roots']),'cited_lexical_entries':len(citations),'citations':citations,'public_abbrev_expansions':abbrev,'prior_compiled_homes_added':sorted(compiledHomes),'ambiguous_source_tokens':{k:sorted(v) for k,v in sorted(ambiguous.items())},'unresolved_qualified_tokens':unresolved.most_common(),'limit':'Static lexical ownership, qualified-name/source declaration index plus prior compiled owner hints; unresolved local/notation tokens retained. Root final compiled inventory is the authoritative supplement. No Lean run or screen.'},indent=2)+'\n')
# Route-evidence comparison cites InputRewind even though the production proofs use existing timed_rewind.
route='TCSlib/Complexity/TuringMachine/Build/InputRewind.lean';assert (wt/route).exists();owners.add(route)
(out/'screen-population-proposed.txt').write_text('\n'.join(sorted(owners))+'\n');(out/'screen-population-proposed.json').write_text(json.dumps({'files':len(owners),'population':sorted(owners),'owned12':R.FILES,'route_evidence_only':[{'path':route,'reason':'matcher-review.md closed-rewind comparison is cited by included peer review evidence'}],'basis':'All144 actual new/changed proof headers/bodies and their leading citations, public-abbrev expansion, prior compiled93-root ownership supplement; no16-file cap. Static candidate ownership is documented; no screen claimed.','all_paths_exist':all((wt/f).exists() for f in owners)},indent=2)+'\n')
# Complete TCSlib retired-name scan, separated into executable code and documentation.
retired=(root/'campaign/fills/mig1/inputs/retired-public-names.txt').read_text().splitlines();shorts=[n.split('.')[-1] for n in retired];pat=re.compile(r"(?<![\w'])"+'(?:'+'|'.join(map(re.escape,shorts))+')'+r"(?![\w'])")
leanhits=[]
for f,s in texts.items():
 for m in pat.finditer(s):
  line=s.count('\n',0,m.start())+1;isc=bool(code[f][m.start():m.end()].strip());leanhits.append({'path':f,'line':line,'name':m[0],'kind':'code' if isc else 'comment','text':s.splitlines()[line-1]})
# Explicit live documentation population: maintained root docs, docs, blueprint and current governance.
live=set(wt.glob('*.md'))
for dirname in ['docs','blueprint']:
 if (wt/dirname).exists():live|={p for p in (wt/dirname).rglob('*') if p.is_file() and p.suffix in ['.md','.tex','.rst']}
for rel in ['campaign/backlog.md','campaign/duplication-ledger.md','campaign/maintainer/START-HERE.md','campaign/maintainer/WORKFLOW.md','campaign/maintainer/HANDOFF.md','campaign/items/roadmap3/PLAN.md']:
 if (wt/rel).exists():live.add(wt/rel)
dochits=[]
for f in sorted(live):
 s=f.read_text()
 for m in pat.finditer(s):
  line=s.count('\n',0,m.start())+1;dochits.append({'path':str(f.relative_to(wt)),'line':line,'name':m[0],'text':s.splitlines()[line-1]})
(out/'live-docs-population.txt').write_text('\n'.join(str(f.relative_to(wt)) for f in sorted(live))+'\n')
ret={'full_TCSlib_files':len(texts),'live_docs_files':len(live),'exact_identifier_boundaries':True,'TCSlib_code_hits':[x for x in leanhits if x['kind']=='code'],'TCSlib_comment_hits':[x for x in leanhits if x['kind']=='comment'],'live_doc_hits':dochits,'historical_exclusion':'Pinned fills/gates/status archives and historical MIG1 design/inventory are preserved as evidence, not live pointers; not rewritten.'}
(out/'retirement-enumeration.json').write_text(json.dumps(ret,indent=2)+'\n');assert not ret['TCSlib_code_hits'],ret['TCSlib_code_hits']
print(json.dumps({'TCSlib_files_indexed':len(texts),'source_proofs':len(R.api['proof_roots']),'citation_entries':len(citations),'proposed_population':len(owners),'extra_over_current22':sorted(owners-set((root/'campaign/fills/mig1/landing/screen-population-DRAFT.txt').read_text().splitlines())),'ambiguous_tokens':len(ambiguous),'retired_code_hits':len(ret['TCSlib_code_hits']),'retired_comment_hits':len(ret['TCSlib_comment_hits']),'live_doc_hits':dochits},indent=2))
