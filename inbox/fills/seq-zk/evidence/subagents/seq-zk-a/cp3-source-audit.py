from pathlib import Path
import subprocess,re,json,hashlib
repo='/Users/seyoonr/.codex/worktrees/seq-zk-proof/tcslib-exchange'
rev='04c253e48d9c0ebb73943f39412365cd4d8e02db'
base='107f1e8c218733eac12d6b9bee6fece441271317'
out=Path('evidence/subagents/seq-zk-a')
names=subprocess.check_output(['git','-C',repo,'diff','--name-only',base,rev,'--','*.lean'],text=True).splitlines()
pattern=re.compile(r'^(?P<private>private\s+)?(?:(?:noncomputable|unsafe|partial|protected)\s+)*(?P<kind>def|abbrev|theorem|lemma|structure|class|instance)\s+(?P<name>[^\s({:]+)')
records=[];sources={}
for file in names:
 text=subprocess.check_output(['git','-C',repo,'show',rev+':'+file],text=True);sources[file]=text
 try: old=subprocess.check_output(['git','-C',repo,'show',base+':'+file],text=True,stderr=subprocess.DEVNULL)
 except subprocess.CalledProcessError:old=''
 oldnames={m.group('name') for l in old.splitlines() if(m:=pattern.match(l))}
 lines=text.splitlines();starts=[]
 for i,line in enumerate(lines):
  if m:=pattern.match(line):starts.append((i,m))
 for index,(i,m) in enumerate(starts):
  finish=starts[index+1][0] if index+1<len(starts) else len(lines)
  # Find the immediately preceding declaration docstring.
  prefix='\n'.join(lines[:i]);docs=list(re.finditer(r'/--[\s\S]*?-/',prefix))
  doc='';docline=None
  if docs:
   last=docs[-1];between=prefix[last.end():]
   if not re.sub(r'@\[[\s\S]*?\]','',between).strip():
    doc=last.group();docline=prefix[:last.start()].count('\n')+1
  body='\n'.join(lines[i:finish]);proofstart=re.search(r':=\s*by\b',body)
  proof=''
  if proofstart:
   proof=body[proofstart.end():]
   proof=re.split(r'\n(?=/--|namespace\b|end\b|section\b)',proof,maxsplit=1)[0]
   proof=proof.rstrip()
  ownnames={sm.group('name') for _,sm in starts}
  readers=[k for k in [m.group('name')+'_eq',m.group('name')+'_iff'] if k in ownnames]
  # Collect the literal declaration region for manual review.
  records.append({'file':file,'line':i+1,'kind':m.group('kind'),'name':m.group('name'),'private':bool(m.group('private')),'new':m.group('name') not in oldnames,'docline':docline,'doc':doc,'proof_lines':len(proof.splitlines()) if proof else 0,'proof_nonblank_lines':len([l for l in proof.splitlines() if l.strip()]),'sketch':'**Proof sketch.**' in doc,'proof_comments':len(re.findall(r'^\s*--',proof,re.M)),'literal_readers':readers,'simps_attr':bool(re.search(r'@\[[^\]]*simps',prefix[-200:])),'region':body})
(out/'cp3-source-audit-inventory.json').write_text(json.dumps({'revision':rev,'base':base,'source_sha256':{p:hashlib.sha256(t.encode()).hexdigest() for p,t in sources.items()},'declarations':records},indent=2)+'\n')
print('Files',len(names),'declarations',len(records),'new',sum(r['new'] for r in records))
print('Missing docs:')
for r in records:
 if r['new'] and not r['private'] and not r['doc'] and r['kind']!='instance':print(r['file'],r['line'],r['kind'],r['name'])
print('Public def/abbrev literal readers:')
for r in records:
 if r['new'] and not r['private'] and r['kind'] in ['def','abbrev']:print(r['file'],r['line'],r['name'],r['literal_readers'],r['simps_attr'])
print('Proofs>=15 with no sketch:')
for r in records:
 if r['new'] and r['proof_lines']>=15 and not r['sketch']:print(r['file'],r['line'],r['name'],r['proof_lines'],r['proof_nonblank_lines'],r['proof_comments'])
print('Proofs>=30 no comments:')
for r in records:
 if r['new'] and r['proof_lines']>=30 and r['proof_comments']==0:print(r['file'],r['line'],r['name'],r['proof_lines'],r['proof_nonblank_lines'])
