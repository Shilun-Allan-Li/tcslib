from pathlib import Path
import subprocess,json,re,difflib,hashlib,collections
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');O=Path('/private/tmp/gate119-round2-return-review');GP='campaign/gates/119-mig1-followup-api';G=R/GP
S='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';B='3023dc1408c3d216fc07a7cbba9ae30135b861ed';C='bf02e7ccd9d0b76d38d4da8d03d31984945fe5b4';OC='c40d52d570953d32b570bf4c9eeecc07e24e23f1'
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def blob(p,f):return git('show',p+':'+f)
def sha(b):return hashlib.sha256(b).hexdigest()
def strip(s):
 # Nested Lean comments are replaced with whitespace, retaining line structure.
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  elif s[i]=='"':
   out.append(' ');i+=1
   while i<len(s):
    if s[i]=='\\':out.extend('  ');i+=2
    elif s[i]=='"':out.append(' ');i+=1;break
    else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  else:out.append(s[i]);i+=1
 assert depth==0;return ''.join(out)
pat=re.compile(r'^\s*(?:(?:@\[[^\]]*\]|noncomputable|unsafe|partial|protected|private)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\b',re.M)
def census(raw):
 s=strip(raw.decode());entries=[]
 for m in pat.finditer(s):
  text=m.group(0);entries.append({'line':s.count('\n',0,m.start())+1,'public':not re.search(r'\bprivate\b',text),'matched':text.strip()})
 return entries
changed=git('diff','--name-only',B,S,'--','*.lean').decode().splitlines();assert len(changed)==5
changes=[];counts=[0,0];owned={}
for p in changed:
 base=blob(B,p);head=blob(S,p);owned[p]=head
 a=base.splitlines(keepends=True);b=head.splitlines(keepends=True)
 ops=[op for op in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes() if op[0]!='equal'];assert len(ops)==1,(p,ops)
 tag,i,j,k,l=ops[0];assert tag in ['insert','delete'];delta=b''.join(b[k:l] if tag=='insert' else a[i:j])
 if tag=='insert':assert b''.join(b[:k]+b[l:])==base
 else:assert b''.join(a[:i]+a[j:])==head
 cs=[census(base),census(head)]
 for z in range(2):counts[z]+=sum(i['public'] for i in cs[z])
 (O/(Path(p).stem+'-delta.lean.txt')).write_bytes(delta)
 changes.append({'path':p,'operation':tag,'base_sha256':sha(base),'head_sha256':sha(head),'delta_bytes':len(delta),'delta_sha256':sha(delta),'public_base':sum(i['public'] for i in cs[0]),'public_head':sum(i['public'] for i in cs[1]),'exact_whole_file_recovery':True})
assert counts==[259,262],counts
assert blob(C,GP+'/source/approved-moved-block.lean.txt')==(O/'Wrappers-delta.lean.txt').read_bytes()
assert len((O/'Wrappers-delta.lean.txt').read_bytes())==1043 and sha((O/'Wrappers-delta.lean.txt').read_bytes())=='3de684d6d30b02098aaf68c8b4223d9d8c92e2ff037505fdd3b5f494412baedf'
assert blob(C,GP+'/source/baseline-removed-block.lean.txt')==(O/'Catalog-delta.lean.txt').read_bytes()
a=(O/'Wrappers-delta.lean.txt').read_bytes().split(b':= by')[0];b=(O/'Catalog-delta.lean.txt').read_bytes().split(b':= by')[0];assert a==b
family=json.loads(blob(C,GP+'/review/audit-return-review/first-entry-family.json'))
quotes=blob(C,GP+'/review/audit-return-review/first-entry-source-quotes.md').decode()
parts=re.findall(r'^## ([^\n]+):([0-9]+) ([^\n]+)\n\n```lean\n(.*?)\n```',quotes,re.M|re.S);assert len(parts)==14
members=[];denoms={}
for path,line,name,block in parts:
 raw=blob(S,path).decode();assert raw.splitlines(keepends=True)[int(line)-1:][0].strip()==block.splitlines()[0].strip()
 start=sum(len(v) for v in raw.splitlines(keepends=True)[:int(line)-1]);assert raw[start:].startswith(block+'\n')
 m=next(m for m in family['members'] if m['name']==name and m['path']==path)
 # The stored quote block hash covers the terminating LF.
 assert m['line']==int(line) and m['block_sha256']==sha((block+'\n').encode()),(name,sha((block+'\n').encode()),m['block_sha256'])
 den=len(census(raw.encode()));assert den==m['source_authored_denominator'],(path,den)
 denoms[path]=den
 members.append({'path':path,'name':name,'line':int(line),'quoted_hash_exact':True,'source_authored_denominator':den})
assert len({(i['path'],i['name']) for i in members})==14
for path,den in denoms.items():assert sum(i['path']==path for i in members)==next(m['family_file_members'] for m in family['members'] if m['path']==path)
part=json.loads(blob(C,GP+'/review/round2-pack/round1-to-round2-input-partition.json'))
for f in part['files']:
 old=blob(f['original_pin'],f['path']);new=blob(S if f['path'].startswith('TCSlib/') and f['path'].endswith('.lean') else C,f['path'])
 assert (len(old),sha(old))==(f['original_bytes'],f['original_sha256'])
 assert (len(new),sha(new))==(f['round2_candidate_bytes'],f['round2_candidate_sha256'])
 assert f['status']==('unchanged' if old==new else 'updated current records; full historical original preserved') if f['status'].startswith('unchanged') else old!=new
historical=[];prefix=GP+'/review/round2-pack/historical-c40/'
for p in part['complete_old_record_captures']:
 assert p.startswith(prefix) and p.endswith('.txt');oldpath=p[len(prefix):-4];v=blob(C,p);assert v==blob(OC,oldpath);historical.append({'path':p,'original_path':oldpath,'bytes':len(v),'sha256':sha(v)})
# Compare all Lean paths, not just the five owner modules, at every claimed identical tree pair.
def leantree(pin):
 out={}
 for ln in git('ls-tree','-r',pin).decode().splitlines():
  meta,path=ln.split('\t');mode,kind,oid=meta.split()
  if path.endswith('.lean'):out[path]=oid
 return out
same=[]
for p,q in [(B,'1160c18f03fd318f0dec25738790935fa61379d4'),(S,'626b1a81ddd33f4b0e0dabd4e874a16a0fe71724'),(B,C),(B,'HEAD')]:
 a=leantree(p);b=leantree(q);assert a==b,(p,q);same.append({'left':p,'right':q,'Lean_files':len(a),'exact_path_blob_equality':True})
assert subprocess.run(['git','-C',str(R),'merge-base','--is-ancestor',B,S]).returncode==0
out={'changed':changes,'public_source_census':counts,'family_members':members,'family_counts':dict(collections.Counter(i['path'] for i in members)),'historical_captures':historical,'same_Lean_trees':same,'base_ancestor':True,'ruling_semantically_reviewed_in_report':True}
(O/'source-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
