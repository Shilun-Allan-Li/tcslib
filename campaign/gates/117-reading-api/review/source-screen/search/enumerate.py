"""Read-only candidate enumeration across pinned local refs/worktree heads.
No fetch, checkout, source write, or payload execution. Candidate enumeration is
not an assertion of exhaustive semantic equivalence."""
from pathlib import Path
import subprocess,json,re,hashlib,datetime,sys,importlib.util
sys.dont_write_bytecode=True
ROOT=Path.cwd();OUT=ROOT/'campaign/gates/117-reading-api/review/source-screen/search'
def git(*args,check=True):
 p=subprocess.run(['git',*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 if check and p.returncode:raise RuntimeError((args,p.stderr.decode()))
 return p
refs=[{'ref':a,'commit':b} for a,b in (line.split() for line in (OUT/'all-local-refs.txt').read_text().splitlines())]
worktrees=(OUT/'worktrees.txt').read_text();heads=[]
for block in worktrees.split('\n\n'):
 p=re.search(r'^worktree (.*)$',block,re.M);h=re.search(r'^HEAD ([0-9a-f]{40})$',block,re.M)
 if p and h:heads.append({'ref':'worktree:'+p.group(1),'commit':h.group(1)})
rows=refs+heads;commits={}
for row in rows:commits.setdefault(row['commit'],[]).append(row['ref'])
trees={};no_tcs=[];pins=[]
for commit,aliases in commits.items():
 git('cat-file','-e',commit+'^{commit}');full=git('rev-parse',commit).stdout.decode().strip();assert full==commit
 tree=git('rev-parse',commit+'^{tree}').stdout.decode().strip();git('cat-file','-e',tree+'^{tree}');t=git('rev-parse',commit+':TCSlib',check=False)
 if t.returncode:no_tcs.append({'commit':commit,'refs':aliases});continue
 subtree=t.stdout.decode().strip();git('cat-file','-e',subtree+'^{tree}');row={'commit':commit,'tree':tree,'tcslib_subtree':subtree,'refs':aliases};pins.append(row);trees.setdefault(subtree,[]).append(row)
namepat=r'(^|[^[:alnum:]_])(toFinTM_eq|leftCfg_(state|inputPos|workTapes|workTapePos|output)|rightCfg_(state|inputPos|workTapes|workTapePos|output)|captureCfg_(state|inputPos|workTapes|workTapePos|output)|branchTM_(k|State|runFrom_independent)|idTM_spaceUsed|constTM_spaceUsed|prependTM_spaceUsed|pairValidTM_spaceUsed)([^[:alnum:]_]|$)'
family=r'leftCfg|rightCfg|captureCfg|toFinTM|branchTM|idTM|constTM|prependTM|pairValidTM|spaceUsed_zero_tapes_eq_zero|runFrom_eq_of_agreeOn'
raw=[];sources={};namehits=[]
for index,(subtree,versions) in enumerate(trees.items(),1):
 commit=versions[0]['commit'];p=git('grep','-n','-I','-E',namepat,commit,'--','TCSlib',check=False);assert p.returncode in [0,1]
 for line in p.stdout.decode().splitlines():
  m=re.match(r'[^:]+:(.*?):(\d+):(.*)',line)
  if m and m[1].endswith('.lean'):namehits.append({'subtree':subtree,'commit':commit,'path':m[1],'line':int(m[2]),'text':m[3]})
 p=git('grep','-l','-I','-E',family,commit,'--','TCSlib',check=False);assert p.returncode in [0,1]
 for line in p.stdout.decode().splitlines():
  path=line.split(':',1)[1]
  if not path.endswith('.lean'):continue
  blob=git('rev-parse',commit+':'+path).stdout.decode().strip()
  rec=sources.setdefault(blob,{'blob':blob,'occurrences':[],'source':None})
  rec['occurrences'].append({'subtree':subtree,'commit':commit,'path':path})
 if index%20==0:print('REF_TREES',index,'/',len(trees),'candidate_blobs',len(sources),flush=True)
(OUT/'ref-pins.json').write_text(json.dumps({'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'ref_rows':len(refs),'worktree_rows':len(heads),'unique_commits':len(commits),'unique_tcslib_subtrees':len(trees),'pins':pins,'without_tcslib':no_tcs,'queries':{'name':namepat,'family':family},'deduplication':'All available local branch/remote refs plus worktree HEAD objects; search each distinct TCSlib subtree once, preserve complete commit/tree/alias pins.'},indent=2)+'\n')
(OUT/'name-candidates.json').write_text(json.dumps(namehits,indent=2)+'\n')
spec=importlib.util.spec_from_file_location('own_parser',ROOT/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
shapes=[];failures=[]
for blob,rec in sources.items():
 text=git('cat-file','blob',blob).stdout.decode();git('cat-file','-e',blob+'^{blob}')
 try:decls=parser.decls(text)
 except Exception as error:failures.append({'blob':blob,'error':str(error),'occurrences':rec['occurrences']});continue
 for d in decls:
  h=d['header'];kinds=[]
  if any(n in h for n in ['leftCfg','rightCfg','captureCfg']) and any('.'+f in h for f in ['state','inputPos','workTapes','workTapePos','output']):kinds.append('configuration fields')
  if 'toFinTM' in h and any(s in h for s in ['State','tm :=','k :=','.k =']):kinds.append('coded bundle/shape')
  if 'spaceUsed' in h and ('= 0' in h or any(n in h for n in ['idTM','constTM','prependTM','pairValidTM'])):kinds.append('zero-space')
  if 'branchTM' in h and any(n in h for n in ['runFrom','.k =','.State =']):kinds.append('branch shape/run')
  if d['name'].endswith('runFrom_eq_of_agreeOn'):kinds.append('generic existing agreement API')
  if kinds:shapes.append({'blob':blob,'name':d['name'],'private':d['private'],'kind':d['kind'],'header':h,'line':d['start'],'end':d['end'],'kinds':kinds,'occurrences':rec['occurrences']})
(OUT/'shape-candidates.json').write_text(json.dumps(shapes,indent=2)+'\n');(OUT/'shape-parser-limitations.json').write_text(json.dumps(failures,indent=2)+'\n');(OUT/'search-summary.json').write_text(json.dumps({'ref_rows':len(refs),'worktree_rows':len(heads),'unique_commits':len(commits),'unique_tcslib_subtrees':len(trees),'candidate_source_blobs':len(sources),'name_hits':len(namehits),'shape_candidates':len(shapes),'parser_failures':len(failures),'no_fetch_or_mutations':True},indent=2)+'\n');print('SEARCH_COMPLETE',len(namehits),'name hits',len(shapes),'shape candidates',len(failures),'parser limitations',flush=True)
