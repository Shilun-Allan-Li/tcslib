from pathlib import Path
import ast,re,sys,os,json,hashlib,collections
B=Path(__file__).resolve().parents[1];cfg=json.loads((B/'qa/config.json').read_text());pop=cfg['population'];Q=B/'qa';(Q/'captures').mkdir()
helper=B/'tools/copy-text-screen-v3.py';tree=ast.parse(helper.read_text());keepFns={'strip','scopes','qualify','body'};keepAssign={'DECL','SCOPE'}
nodes=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom))or isinstance(n,ast.FunctionDef)and n.name in keepFns or isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in keepAssign for t in n.targets)]
ns={};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'),ns)
def mappedStrip(src):
 out=[];pos=[];i=0;depth=0
 while i<len(src):
  if src.startswith('/-',i):depth+=1;i+=2;continue
  if depth and src.startswith('-/',i):depth-=1;i+=2;continue
  if depth:i+=1;continue
  if src.startswith('--',i):
   j=src.find('\n',i);i=len(src)if j<0 else j;continue
  out.append(src[i]);pos.append(i);i+=1
 return ''.join(out),pos
nbase=collections.Counter(Path(p).name for p in pop);indices={};fileRows=[]
for phase in ['BASE','HEAD']:
 root=Path(cfg[phase+'_export']);rows=[]
 for p in pop:
  raw=(root/p).read_text();t,pos=mappedStrip(raw);assert t==ns['strip'](raw)
  dest=Q/'captures'/phase/Path(p+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(raw)
  ms=list(ns['DECL'].finditer(t));ev=ns['scopes'](p,t);found=[]
  for i,m in enumerate(ms):
   stop=ms[i+1].start()if i+1<len(ms)else len(t);kind='proof'if m.group(2)in ['theorem','lemma']else'term';bd=re.sub(r'\s+','',ns['body'](t[m.start():stop]));namespace=[n for o,n in ev if o<=m.start()][-1]
   if len(bd)>=60:found.append({'stripped_start':m.start(),'stripped_end':stop,'short':m.group(3),'qualified':ns['qualify'](namespace,m.group(3)),'kind':kind,'normalized_body_len':len(bd),'normalized_body_SHA256':hashlib.sha256(bd.encode()).hexdigest()})
  short=collections.Counter(r['short']for r in found);qual=collections.Counter(r['qualified']for r in found);seen={}
  for r in found:
   if short[r['short']]==1:name=r['short']
   elif qual[r['qualified']]==1:name=r['qualified']
   else:seen[r['qualified']]=seen.get(r['qualified'],0)+1;name=r['qualified']+'#'+str(seen[r['qualified']])
   start=pos[r['stripped_start']];end=pos[r['stripped_end']-1]+1 if r['stripped_end']>r['stripped_start']else start
   lab=(Path(p).name if nbase[Path(p).name]==1 else p)+'::'+name
   rows.append({'screen_label':lab,'path':p,'name':name,'kind':r['kind'],'capture':str(dest.relative_to(B)),'original_start_char':start,'original_end_char':end,'original_start_line':raw.count('\n',0,start)+1,'original_end_line':raw.count('\n',0,end)+1,'stripped_start':r['stripped_start'],'stripped_end':r['stripped_end'],'normalized_body_len':r['normalized_body_len'],'normalized_body_SHA256':r['normalized_body_SHA256']})
  fileRows.append({'phase':phase,'path':p,'capture':str(dest.relative_to(B)),'UTF8_bytes':len(raw.encode()),'SHA256':hashlib.sha256(raw.encode()).hexdigest(),'screen_eligible_declarations':len(found)})
 assert len({r['screen_label']for r in rows})==len(rows)
 indices[phase]=rows;(Q/(phase+'-declaration-capture-index.json')).write_text(json.dumps({'status':'LEXICAL CAPTURE PREPARATION ONLY; no lcs/tiled/pair matching run','parser_source_SHA256':hashlib.sha256(helper.read_bytes()).hexdigest(),'source_root':str(root),'population':pop,'declarations':rows,'offset_unit':'Python Unicode character offset in full captured source; source SHA256 binds UTF8 bytes'},indent=2)+'\n')
baseText=(Q/'screen-BASE.txt').read_text();stats=re.search(r'declarations screened: (\d+); copy pairs .*: (\d+); reproduced text: ([\d,]+) chars',baseText);assert stats and int(stats[1])==len(indices['BASE'])
labels={r['screen_label']:r for r in indices['BASE']};pairs=[]
for line in baseText.splitlines():
 m=re.match(r'^\s+(\S+::\S+)\s+reproduces\s+(\S+::\S+): (\d+)/(\d+) = (\d+)%',line)
 if m:
  assert m[1]in labels and m[2]in labels,(m[1],m[2]);pairs.append({'target':labels[m[1]],'source':labels[m[2]],'reproduced':int(m[3]),'source_length':int(m[4]),'percent':int(m[5]),'raw_line':line})
assert len(pairs)==int(stats[2])
(Q/'BASE-screen-all-pair-capture-map.json').write_text(json.dumps({'source_screen':'qa/screen-BASE.txt','all_pairs_mapped':True,'pairs':pairs},indent=2)+'\n')
(Q/'MAPPED-CAPTURES.json').write_text(json.dumps({'complete_population_per_phase':33,'files':fileRows,'BASE_actual_screen':{'declarations':int(stats[1]),'pairs':int(stats[2]),'reproduced_chars':int(stats[3].replace(',',''))},'HEAD_status':'Only captures/index prepared; actual screen and pairdiff pending root lock execution','no_new_screen_executed':True},indent=2)+'\n')
print(json.dumps({'BASE_captured_eligible_declarations':len(indices['BASE']),'HEAD_captured_eligible_declarations':len(indices['HEAD']),'BASE_actual_pairs_all_mapped':len(pairs),'full_file_captures':len(fileRows),'new_screen_executed':False}))
