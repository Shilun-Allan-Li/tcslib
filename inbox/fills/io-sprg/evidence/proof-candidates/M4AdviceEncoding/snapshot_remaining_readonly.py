from pathlib import Path
import csv,hashlib,io,json,re
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B=Path('/private/tmp/io-sprg-proof-notes/M4AdviceEncoding')

def strip(s):
 out=[];i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif quoted:
   if s[i]=='\\':out.extend('  ');i+=2
   elif s[i]=='"':quoted=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i)
   if j<0:out.extend(' '*(len(s)-i));i=len(s)
   else:out.extend(' '*(j-i));i=j
  elif s[i]=='"':quoted=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)

prefix='TCSlib.Cryptography.Obfuscation.StructuredSeed'
found={};bindings={}
for p in sorted((W/'TCSlib/Cryptography/Obfuscation/StructuredSeed').glob('**/*.lean')):
 s=p.read_text();code=strip(s);lines=code.splitlines();stack=[];commands=[]
 bindings[str(p.relative_to(W))]=hashlib.sha256(p.read_bytes()).hexdigest()
 for n,line in enumerate(lines,1):
  ns=re.match(r'^namespace\s+(\S+)',line)
  if ns:stack.append(ns.group(1));commands.append((n,None));continue
  if re.match(r'^section(?:\s|$)',line):stack.append(None);commands.append((n,None));continue
  if re.match(r'^end(?:\s|$)',line):
   if stack:stack.pop()
   commands.append((n,None));continue
  m=re.match(r'^(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s(:]+)',line)
  if m:
   leaf=m.group(2);name='.'.join([x for x in stack if x is not None]+[leaf])
   if leaf.startswith('_root_.'):name=leaf.removeprefix('_root_.')
   commands.append((n,name))
 for j,(n,name) in enumerate(commands):
  if name is None:continue
  end=commands[j+1][0]-1 if j+1<len(commands) else len(lines)
  text='\n'.join(lines[n-1:end])
  if name in found:raise RuntimeError('duplicate '+name)
  found[name]={'current_file_line':str(p.relative_to(W))+':'+str(n),
               'direct_sorry':bool(re.search(r'\bsorry\b',text)),
               'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
frozen=list(csv.DictReader((W/'evidence/statements/proof-obligations-current.tsv').open(),delimiter='\t'))
missing=[r['Lean_name'] for r in frozen if r['Lean_name'] not in found]
assert not missing,missing
remaining=[dict(r,**found[r['Lean_name']]) for r in frozen if found[r['Lean_name']]['direct_sorry']]
assert len(remaining)==32,len(remaining)
stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=list(remaining[0]),delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(remaining)
(B/'remaining32-source-inventory.tsv').write_text(stream.getvalue())
counts={}
for r in remaining:counts[r['milestone']]=counts.get(r['milestone'],0)+1
(B/'remaining32-source-snapshot.json').write_text(json.dumps({'status':'STATIC_DIRECT_SORRY_INVENTORY_NOT_KERNEL_CENSUS',
 'original_frozen_total':len(frozen),'remaining_original':32,'by_frozen_milestone':counts,
 'original_complete_in_source':len(frozen)-32,'missing_frozen_names':missing,
 'source_sha256':bindings,'note':'Source text status only; no assertion of checked proofs, a git HEAD, final census or transitive sorry dependencies.'},indent=2)+'\n')
print('Original remaining32:',counts)
