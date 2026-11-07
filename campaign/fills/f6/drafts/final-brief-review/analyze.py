from pathlib import Path
import re,json,hashlib,collections
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
WT=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-natbits')
PACK=OUT.parent/'packet-preparation'
sha=lambda b:hashlib.sha256(b).hexdigest()
def strip_comments(s):
 result=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;result.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;result.extend('  ');i+=2
   else:result.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;result.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;result.extend(' '*(j-i));i=j
  else:result.append(s[i]);i+=1
 assert depth==0
 return ''.join(result)
def imports(s):
 result=[]
 for line in strip_comments(s).splitlines():
  t=line.strip()
  if not t:continue
  if t.startswith('import '):result+=t[7:].split()
  elif t.startswith('public import '):result+=t[14:].split()
  else:break
 return result
mods={}
source={}
for p in sorted((WT/'TCSlib').rglob('*.lean')):
 m=str(p.relative_to(WT)).removesuffix('.lean').replace('/','.');source[m]=p;mods[m]=imports(p.read_text())
mods['TCSlib']=imports((WT/'TCSlib.lean').read_text())
TARGET='TCSlib.Complexity.SpaceComplexity.Hierarchy'
rev=collections.defaultdict(set)
for m,im in mods.items():
 for i in im:rev[i].add(m)
def closure(start,neighbors):
 seen=set();todo=list(start)
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(i for i in neighbors(n) if i in mods)
 return seen-{'TCSlib'}
boot=closure([TARGET],lambda m:mods[m]);down=closure([TARGET],lambda m:rev[m]);final=closure(down,lambda m:mods[m])
math=sorted({i for m in final for i in mods[m] if i.startswith('Mathlib.')})
external=sorted({i for m in final for i in mods[m] if not i.startswith('TCSlib.')})
orders={};checks={}
for filename,expected in [('bootstrap-order.txt',boot),('downstream-order.txt',down),('final-order.txt',final)]:
 rows=(PACK/filename).read_text().splitlines();names=[x.replace('/','.') for x in rows];pos={m:i for i,m in enumerate(names)}
 assert len(names)==len(set(names)) and set(names)==expected
 bad=[(m,i) for m in names for i in mods[m] if i in pos and pos[i]>=pos[m]];assert not bad
 orders[filename]=len(names);checks[filename]={'exact_module_set':True,'no_duplicates':True,'all_internal_imports_earlier':True}
assert (PACK/'mathlib-roots.txt').read_text().splitlines()==math
assert (PACK/'external-imports.txt').read_text().splitlines()==external
rows=json.loads((PACK/'source-inputs.json').read_text());assert len(rows)==len(final)
assert {x['path'].removesuffix('.lean').replace('/','.') for x in rows}==final
for row in rows:
 data=(WT/row['path']).read_bytes();assert sha(data)==row['sha256'];assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob'];assert imports(data.decode())==row['imports']
raw=(WT/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean').read_text()
assert raw==(PACK/'Hierarchy.lean.txt').read_text()
sorries=[i for i,l in enumerate(raw.splitlines(),1) if re.search(r'\bsorry\b',l)]
assert sorries==[159] and len(re.findall(r'\bsorry\b',raw))==1
header=raw[raw.index('theorem space_universal :'):raw.index(':= by',raw.index('theorem space_universal :'))].rstrip()
stored=(PACK/'space_universal-header.txt').read_text().rstrip();assert header==stored
summary={'orders':orders,'Mathlib_roots':len(math),'external_imports':external,'checks':checks,'all_229_current_source_bytes_imports_and_git_blob_hashes_match_packet':True,'Git_commit_object_NOT_independently_checked':True,'source_only_admission_inventory':{'raw_sorry_token_count':1,'lines':sorries,'not_compiled_axiom_audit':True},'target_header_sha256':sha((PACK/'space_universal-header.txt').read_bytes()),'root_TCSlib_excluded':True}
(OUT/'graph-crosscheck.json').write_text(json.dumps(summary,indent=2)+'\n')
# Closed final probe inputs; pending v5/v6 are listed separately and no result is inferred.
probe_paths=[]
for name in ['Final-native','Final-return','Final-layout','Final-bundle','Final-zero-outer','Final-correction']:
 probe_paths.append(OUT.parent/'layout-preship-v2'/(name+'.lean.txt'))
probe_paths.append(OUT.parent/'first-header-preship-v3'/'First-header-sealed-v3.lean.txt')
for folder in ['header-host-handoff-v4','ledger-contract-preship-v7','final-seam-preship-v5']:
 probe_paths.append(OUT.parent/folder/'Final-sealed.lean.txt')
docs=[OUT.parent/'f6-fill.DRAFT.md',OUT.parent/'ROUTE-ASSESSMENT.md']
probe_imports={str(p.relative_to(ROOT)):imports(p.read_text()) for p in probe_paths}
extra_tcs=sorted({i for im in probe_imports.values() for i in im if i.startswith('TCSlib.') and i not in boot})
extra_math=sorted({i for im in probe_imports.values() for i in im if i.startswith('Mathlib.') and i not in math})
assert not extra_tcs and not extra_math
(OUT/'probe-import-crosscheck.json').write_text(json.dumps({'completed_probe_imports':probe_imports,'extra_TCSlib_roots_beyond_target_bootstrap':extra_tcs,'extra_direct_Mathlib_cache_roots_beyond_final65':extra_math,'limits':'Imports only; no native Lean or cache replay. Final v5/v6 evidence remains pending and must be incorporated when frozen.'},indent=2)+'\n')
# Reproducible conservative lexical declaration/home candidates. Comments stripped from proofs,
# retained in docs because public-name mentions prescribe route steps. Suffix collisions remain explicit.
decls=collections.defaultdict(list)
for m,p in source.items():
 clean=strip_comments(p.read_text())
 for mt in re.finditer(r'(?m)^\s*(?:(?:noncomputable|private|protected)\s+)*(?:def|abbrev|lemma|theorem|structure|inductive|class)\s+([A-Za-z_][A-Za-z_0-9.\u2080-\u2089\u208a\u208b]*)',clean):
  line=clean[:mt.start()].count('\n')+1
  for key in {mt.group(1),mt.group(1).split('.')[-1]}:decls[key].append({'module':m,'source':str(p.relative_to(WT)),'name_as_written':mt.group(1),'line':line})
mentions=collections.defaultdict(list)
for p in docs+probe_paths:
 text=p.read_text() if p in docs else strip_comments(p.read_text())
 for token in sorted(set(re.findall(r'[A-Za-z_][A-Za-z_0-9.\u2080-\u2089\u208a\u208b]*',text))):
  if not ('.' in token or '_' in token or len(token)>=8):continue
  keys=[token,token.removeprefix('Turing.'),token.removeprefix('Complexity.'),token.split('.')[-1]]
  matches=[]
  for k in keys:
   if k in decls:matches=decls[k];break
  for row in matches:
   mentions[row['source']].append({'token':token,'evidence':str(p.relative_to(ROOT)),'decl':row})
(OUT/'cited-source-candidates.json').write_text(json.dumps(dict(sorted(mentions.items())),indent=2)+'\n')
inputs={str(p.relative_to(ROOT)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in docs+probe_paths+[ROOT/'campaign/fills/f6/STATUS.md']+list(PACK.iterdir()) if p.is_file()}
(OUT/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
print(json.dumps({'bootstrap':len(boot),'downstream':len(down),'final':len(final),'Mathlib':len(math),'raw_sorry':sorries,'candidate_source_homes':list(sorted(mentions))},indent=2))
