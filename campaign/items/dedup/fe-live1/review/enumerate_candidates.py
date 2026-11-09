from pathlib import Path
import re,json,hashlib,collections,bisect
O=Path(__file__).parent

def strip(s):
 a=[];i=0;dep=0;line=False;string=False
 while i<len(s):
  c=s[i];n=s[i:i+2]
  if line:
   a.append('\n' if c=='\n' else ' ');line=c!='\n';i+=1;continue
  if dep:
   if n=='/-':dep+=1;a.extend('  ');i+=2
   elif n=='-/':dep-=1;a.extend('  ');i+=2
   else:a.append('\n' if c=='\n' else ' ');i+=1
   continue
  if string:
   a.append(c)
   if c=='\\' and i+1<len(s):a.append(s[i+1]);i+=2;continue
   if c=='"':string=False
   i+=1;continue
  if n=='--':line=True;a.extend('  ');i+=2;continue
  if n=='/-':dep=1;a.extend('  ');i+=2;continue
  if c=='"':string=True
  a.append(c);i+=1
 return ''.join(a)
decl=re.compile(r'(?m)^(?:@\[[^\n]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*)?(?P<kind>def|abbrev|lemma|theorem|instance|structure|inductive|class)\s+(?P<name>[^\s:({\[]+)')
needles={'Nat.find':re.compile(r'\bNat\.find(?:\b|_)'),'iterate_fixed':re.compile(r'\b(?:Function\.)?iterate_fixed\b'),'canonical_call':re.compile(r'\bexists_first_entry_of_fixed\b')}
rows=[];blocks=O/'blocks';blocks.mkdir(exist_ok=True)
for f in sorted((O/'source').rglob('*.lean.txt')):
 text=f.read_text();code=strip(text);ds=list(decl.finditer(code));begins=[d.start() for d in ds];groups={}
 for kind,pat in needles.items():
  for m in pat.finditer(code):
   di=bisect.bisect_right(begins,m.start())-1
   if di<0:continue
   groups.setdefault(di,[]).append({'kind':kind,'line':code.count('\n',0,m.start())+1,'text':text.splitlines()[code.count('\n',0,m.start())].strip()})
 for di,hits in sorted(groups.items()):
  d=ds[di];start=d.start();end=ds[di+1].start() if di+1<len(ds) else len(text)
  # Last non-comment token before next declaration is sufficient for source-review chunks.
  end=start+len(code[start:end].rstrip());chunk=text[start:end]+'\n';path=str(f.relative_to(O/'source'))[:-4]
  row={'id':len(rows)+1,'path':path,'name':d['name'],'kind':d['kind'],'private':'private' in (d['mods'] or '').split(),'line':code.count('\n',0,start)+1,'end_line':code.count('\n',0,end)+1,'hits':sorted(hits,key=lambda h:(h['line'],h['kind'])),'chunk_sha256':hashlib.sha256(chunk.encode()).hexdigest()}
  filename=f"{row['id']:03d}-{Path(path).stem}-{re.sub(r'[^a-zA-Z0-9_-]','_',d['name'])}.lean.txt";(blocks/filename).write_text(chunk);row['block']='blocks/'+filename;rows.append(row)
(O/'candidate-declarations.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
summary={'source':json.loads((O/'SOURCE-ENDPOINT.json').read_text())['source'],'source_files':json.loads((O/'SOURCE-ENDPOINT.json').read_text())['Lean_files'],'raw_search':'311 raw Nat.find/first-entry/first-arrival/first-stop hits retained uncapped in candidate-hits-all.txt','code_candidate_declarations':len(rows),'files':dict(collections.Counter(r['path'] for r in rows)),'code_hit_kinds':dict(collections.Counter(h['kind'] for r in rows for h in r['hits'])),'limits':'Own lexical candidate enumeration plus inspection. No canonical copy-text screen or Lean execution; not semantic/exhaustive absence.'};(O/'ENUMERATION.json').write_text(json.dumps(summary,indent=2)+'\n')
for r in rows:print(r['id'],r['path'],r['name'],r['line'],sorted(set(h['kind'] for h in r['hits'])))
print('SUMMARY',json.dumps(summary))
