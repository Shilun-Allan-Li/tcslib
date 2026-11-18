"""Refresh a static checkpoint snapshot. No Lean, git, cache, source writes or REPORT writes."""
from pathlib import Path
from datetime import datetime,timezone
from collections import Counter
import csv,hashlib,json,re
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
out=Path('/private/tmp/io-sprg-proof-notes/M1CheckpointDraft')
area=repo/'TCSlib/Cryptography/Obfuscation/StructuredSeed'
paths=sorted(area.rglob('*.lean'))+[
 repo/'TCSlib/Cryptography/Obfuscation/StructuredSeed.lean',
 repo/'TCSlib/Cryptography/Obfuscation.lean']
blobs={p:p.read_bytes()for p in paths}
def strip(s):
 a=[];i=0;d=0;q=False
 while i<len(s):
  if d:
   if s.startswith('/-',i):d+=1;i+=2
   elif s.startswith('-/',i):d-=1;i+=2
   else:
    a.append('\n'if s[i]=='\n'else' ');i+=1
  elif q:
   if s[i]=='\\':a.extend('  ');i+=2
   elif s[i]=='"':q=False;a.append(' ');i+=1
   else:a.append('\n'if s[i]=='\n'else' ');i+=1
  elif s.startswith('/-',i):d=1;a.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i)
   if j<0:a.extend(' '*(len(s)-i));i=len(s)
   else:a.extend(' '*(j-i));i=j
  elif s[i]=='"':q=True;a.append(' ');i+=1
  else:a.append(s[i]);i+=1
 return ''.join(a)
oldhash={}
for l in(repo/'evidence/build/summary.txt').read_text().splitlines():
 m=re.match(r'^(TCSlib/\S+) .*source=([0-9a-f]{64}) ',l)
 if m:oldhash[m[1]+'.lean']=m[2]
files=[];decls={};holes=[]
for p,data in blobs.items():
 rel=p.relative_to(repo).as_posix();s=data.decode();code=strip(s);lines=code.splitlines()
 starts=[]
 for i,l in enumerate(lines):
  m=re.match(r'^(?:noncomputable\s+)?(theorem|def|abbrev|structure|instance)\s+([^\s(:]+)',l)
  if m:starts.append((i,m[1],m[2]))
 lookup=[]
 for k,(i,kind,name)in enumerate(starts):
  end=starts[k+1][0]if k+1<len(starts)else len(lines)
  text='\n'.join(lines[i:end])
  h=bool(re.search(r'\bsorry\b',text))
  lookup.append({'name':name,'line':i+1,'kind':kind,'direct_sorry':h})
  if h:holes.append({'file':rel,'name':name,'line':i+1})
 decls[rel]=lookup
 sh=hashlib.sha256(data).hexdigest()
 files.append({'file':rel,'sha256':sh,'M0_sha256':oldhash.get(rel),
  'M0_status':'NEW'if rel not in oldhash else('UNCHANGED'if oldhash[rel]==sh else'CHANGED'),
  'lines':len(s.splitlines()),'max_width':max(map(len,s.splitlines()),default=0),
  'direct_sorry_tokens':len(re.findall(r'\bsorry\b',code))})
obligations=[]
for row in csv.DictReader((repo/'evidence/statements/proof-obligations-current.tsv').open(),delimiter='\t'):
 rel,oldline=row['file_line'].rsplit(':',1);short=row['Lean_name'].rsplit('.',1)[-1]
 found=[d for d in decls[rel]if d['name']==short or d['name'].endswith('.'+short)]
 if len(found)!=1:raise RuntimeError((row['Lean_name'],found))
 d=found[0];obligations.append({'name':row['Lean_name'],'file':rel,'current_line':d['line'],
  'milestone':row['milestone'],'direct_sorry':d['direct_sorry']})
checks=[]
modules={'M1-degree':'Degree','M1-Params':'Params','M1-Encoding':'Encoding','M1-LPN':'LPN',
 'M1-Basic':'Basic','M1-Buckets':'Buckets','M1-SparseFactor':'SparseFactor','M1-Polys':'Polys',
 'M1-Correctness':'Correctness','M1-Defs':'Defs','M1-Samplers':'Samplers'}
for folder,leaf in modules.items():
 p=repo/'evidence/checks'/folder/'summary.json'
 if not p.exists():continue
 s=json.loads(p.read_text());source=area/(leaf+'.lean')
 checks.append({'summary':str(p.relative_to(repo)),'module':leaf,
   'source_hash_matches':hashlib.sha256(blobs[source]).hexdigest()==s.get('source_sha256'),
   'all_standard_axioms':s.get('all_standard_axioms'),
   'frozen_statements_unchanged':s.get('frozen_statements_unchanged',s.get('no_frozen_statement_changes')),
   'public_theorems':s.get('public_theorems'),'new_helpers':s.get('new_helpers')})
steps=[]
for p in(repo/'evidence/steps').glob('*/step.json'):
 try:s=json.loads(p.read_text())
 except json.JSONDecodeError:continue
 steps.append({'id':p.parent.name,'name':s.get('name'),'status':s.get('status'),'check':s.get('check')})
classes={}
for phase in sorted(set(r['milestone']for r in obligations)):
 rs=[r for r in obligations if r['milestone']==phase]
 classes[phase]={'M0_original':len(rs),'source_filled':sum(not r['direct_sorry']for r in rs),
                 'source_remaining':sum(r['direct_sorry']for r in rs)}
# Current named additions: source theorem commands, not an inferred kernel census.
new=[]
for f,ds in decls.items():
 for d in ds:
  if (f.endswith('/Basic.lean')and d['kind']=='theorem')or d['name']in('G4_seed_allOutputs','Params.G4_seed_allOutputs'):
   new.append(dict(file=f,**d))
result={'status':'STATIC_SOURCE_SNAPSHOT_NOT_KERNEL_CENSUS','captured_utc':datetime.now(timezone.utc).isoformat(),
 'M0_head':(repo/'evidence/freeze/M0.txt').read_text().strip(),
 'latest_recorded_progress':json.loads((repo/'evidence/checkpoints/M1/progress.json').read_text()),
 'source_files':len(files),'source_lines':sum(r['lines']for r in files),
 'max_lines':max(r['lines']for r in files),'max_width':max(r['max_width']for r in files),
 'direct_sorry_tokens':sum(r['direct_sorry_tokens']for r in files),
 'M0_original_obligations':len(obligations),'M0_original_filled':sum(not r['direct_sorry']for r in obligations),
 'M0_original_remaining':sum(r['direct_sorry']for r in obligations),
 'by_milestone':classes,'new_named_theorems':new,'owner_summaries':checks,
 'recorded_step_count':len(steps),'recorded_step_statuses':dict(Counter(r['status']for r in steps)),
 'latest_steps':sorted(steps,key=lambda x:x['id'])[-8:],
 'files':files,'obligations':obligations,'source_holes':holes,
 'changed_while_reading':[str(p.relative_to(repo))for p,v in blobs.items()if p.read_bytes()!=v]}
(out/'snapshot.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
with(out/'source-obligations.tsv').open('w')as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['name','file','line','milestone','source_status'])
 for r in obligations:w.writerow([r['name'],r['file'],r['current_line'],r['milestone'],'SORRY'if r['direct_sorry']else'BODY_PRESENT_NOT_NEW_KERNEL_CLAIM'])
print(json.dumps({k:result[k]for k in('captured_utc','source_files','source_lines','direct_sorry_tokens','M0_original_filled','M0_original_remaining','by_milestone','recorded_step_count','changed_while_reading')},ensure_ascii=False))
