# Read-only source lookup for already root-run screen labels; no pair comparison/scoring.
from pathlib import Path
import re,json,hashlib,collections
O=Path(__file__).parent;population=(O/'screen-population.txt').read_text().splitlines();DECL=re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)',re.M);SCOPE=re.compile(r'^[ \t]*(?:(namespace)[ \t]+(\S+)|(?:noncomputable[ \t]+)?(section)\b[ \t]*([^\s]*)|(mutual)\b|(end)\b[ \t]*([^\s]*))',re.M)
def strip_map(src):
 out=[];mapping=[];i=0;depth=0
 while i<len(src):
  if src.startswith('/-',i):depth+=1;i+=2;continue
  if depth and src.startswith('-/',i):depth-=1;i+=2;continue
  if depth:i+=1;continue
  if src.startswith('--',i):
   j=src.find('\n',i);i=len(src) if j<0 else j;continue
  out.append(src[i]);mapping.append(i);i+=1
 assert depth==0;return ''.join(out),mapping

def body(b):
 depth=0
 for i,ch in enumerate(b):
  if ch in '([{⟨':depth+=1
  elif ch in ')]}⟩':depth-=1
  elif b.startswith(':=',i) and depth==0:return b[i+2:]
 depth=0
 for i,ch in enumerate(b):
  if ch in '([{⟨':depth+=1
  elif ch in ')]}⟩':depth-=1
  elif depth==0 and (ch=='|' or re.match(r'\bwhere\b',b[i:i+6])):return b[i:]
 return ''
counts={};namecounts=collections.Counter(Path(p).name for p in population)
for side in ['BASE','HEAD']:
 result=[]
 for path in population:
  raw=(O/'source'/side/(path+'.txt')).read_text();t,mapping=strip_map(raw);stack=[];events=[(0,'')]
  for m in SCOPE.finditer(t):
   if m.group(1):stack.extend(('namespace',c) for c in m.group(2).split('.'))
   elif m.group(3):stack.append(('section',m.group(4)))
   elif m.group(5):stack.append(('mutual',''))
   else:
    for c in reversed(m.group(7).split('.')):assert stack and stack[-1][1]==c,(path,c,stack);stack.pop()
   events.append((m.end(),'.'.join(n for k,n in stack if k=='namespace')))
  matches=list(DECL.finditer(t));found=[];allseen=collections.Counter()
  for i,m in enumerate(matches):
   end=matches[i+1].start() if i+1<len(matches) else len(t);ns=[n for at,n in events if at<=m.start()][-1];name=m.group(3);qualified=name[len('_root_.'):] if name.startswith('_root_.') else ns+'.'+name if ns else name;allseen[qualified]+=1;norm=re.sub(r'\s+','',body(t[m.start():end]));start_raw=mapping[m.start()];end_raw=mapping[end] if end<len(mapping) else len(raw)
   if len(norm)>=60:found.append({'path':path,'source_commit':json.loads((O/'scope.json').read_text())[side],'short_name':name,'qualified_name':qualified,'occurrence_all_declarations':allseen[qualified],'kind':'proof' if m.group(2) in ('theorem','lemma') else 'term','raw_decl_start':start_raw,'raw_v3_span_end':end_raw,'source_start_line':raw[:start_raw].count('\n')+1,'normalized_body':norm,'normalized_chars':len(norm),'normalized_body_sha256':hashlib.sha256(norm.encode()).hexdigest(),'complete_source_sha256':hashlib.sha256(raw.encode()).hexdigest()})
  short=collections.Counter(r['short_name'] for r in found);qual=collections.Counter(r['qualified_name'] for r in found);seen=collections.Counter()
  for r in found:
   name=r['short_name']
   if short[name]>1:
    name=r['qualified_name']
    if qual[name]>1:seen[name]+=1;name+='#'+str(seen[name])
   label=(Path(path).name if namecounts[Path(path).name]==1 else path)+'::'+name;r['label']=label;r['canonical_source_identity']=[path,r['qualified_name'],r['occurrence_all_declarations']];result.append(r)
 assert len({r['label'] for r in result})==len(result);(O/'preparation'/(side+'-screen-label-source-index.json')).write_text(json.dumps(result,indent=2)+'\n');counts[side]=len(result)
(O/'preparation/screen-label-lookup-scope.json').write_text(json.dumps({'scope':'Source lookup for root-run output labels using exact declared source/extraction conventions. Does not compute LCS, grams, tiling, scores or pairs and is not a screen execution.','source_population':44,'filtered_source_lookup_counts':counts,'no_Lean_or_screen_run':True},indent=2)+'\n');print('Prepared source-only label lookups',counts,'without pair scoring.')
