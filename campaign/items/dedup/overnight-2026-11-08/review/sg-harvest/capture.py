from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');O=Path('/private/tmp/ab34-overnight-sg1-harvest')
def sha(b):return hashlib.sha256(b).hexdigest()
def imports(s):
 k=0;out=[]
 while k<len(s):
  if s[k].isspace():k+=1
  elif s.startswith('--',k):
   e=s.find('\n',k);k=len(s) if e<0 else e+1
  elif s.startswith('/-',k):
   depth=1;k+=2
   while k<len(s) and depth:
    if s.startswith('/-',k):depth+=1;k+=2
    elif s.startswith('-/',k):depth-=1;k+=2
    else:k+=1
  elif s.startswith('import ',k):
   e=s.find('\n',k);e=len(s) if e<0 else e;out+=s[k+7:e].split('--')[0].split();k=e+1
  else:break
 return out
allrows=[];graph={};selected=[];declarations=[]
for p in sorted(R.glob('TCSlib/**/*.lean')):
 rel=str(p.relative_to(R));b=p.read_bytes();s=b.decode();mod=rel[:-5].replace('/','.');imps=imports(s);graph[mod]=imps
 allrows.append({'path':rel,'bytes':len(b),'sha256':sha(b),'blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),'imports':imps})
 keep=(rel.startswith('TCSlib/Complexity/TuringMachine/Build/') or rel in {'TCSlib/Complexity/TuringMachine/Finite.lean','TCSlib/Complexity/TuringMachine/Deterministic.lean','TCSlib/Complexity/TuringMachine/Configuration.lean','TCSlib/Complexity/TuringMachine/Composition.lean','TCSlib/Complexity/TuringMachine/Encoding.lean','TCSlib/Complexity/TuringMachine/StateRenaming.lean','TCSlib/Complexity/ClassNP/SAT.lean','TCSlib/Complexity/ClassNP/Tautology.lean','TCSlib/Complexity/CookLevin/Hardness.lean','TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean','TCSlib/Complexity/ClassP/BinaryArith/ExhaustiveReplay.lean','TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean'} or rel.startswith('TCSlib/Complexity/ClassNP/PolyTime'))
 if keep:
  q=O/'source'/(rel+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);selected.append(rel)
  matches=list(re.finditer(r'(?m)^(?P<mods>(?:(?:private|protected|noncomputable) )*)(?P<kind>def|abbrev|lemma|theorem|structure|inductive|class|instance)\s+(?P<name>[^\s(:{]+)',s))
  for i,m in enumerate(matches):
   e=matches[i+1].start() if i+1<len(matches) else len(s);block=s[m.start():e];doc=s.rfind('/--',0,m.start());chunkstart=doc if doc>=0 and s[doc:m.start()].count('/--')==1 and s[doc:m.start()].count('-/')==1 else m.start()
   chunk=s[chunkstart:e]
   declarations.append({'path':rel,'name':m['name'],'kind':m['kind'],'private':'private' in m['mods'].split(),'line':s.count('\n',0,m.start())+1,'end_line':s.count('\n',0,e)+1,'header':block.split(':=',1)[0].strip(),'chunk':chunk,'chunk_sha256':sha(chunk.encode()),'source_sha256':sha(b)})
(O/'all-source-hashes-and-imports.json').write_text(json.dumps({'root_supplied_campaign_pin':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','note':'No Git query; captures/hash map bind read bytes, root supplies actual commit provenance.','captured_utc':datetime.now(timezone.utc).isoformat(),'files':allrows},indent=2)+'\n')
(O/'captured-population.json').write_text(json.dumps({'files':selected,'capture_files':len(selected),'scope':'fixed explicit Build/all PolyTime plus named client/run/API homes; candidate enumeration, not exhaustive semantic library audit'},indent=2)+'\n')
(O/'declaration-inventory.json').write_text(json.dumps(declarations,indent=2,ensure_ascii=False)+'\n')
(O/'import-graph.json').write_text(json.dumps(graph,indent=2)+'\n')
print(json.dumps({'all_Lean_files':len(allrows),'source_captures':len(selected),'lexical_declarations':len(declarations),'source_bytes':sum((R/f).stat().st_size for f in selected)}))
