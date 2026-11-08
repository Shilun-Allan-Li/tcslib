from pathlib import Path
import subprocess,re,json,hashlib
P=Path('/private/tmp/sg1-round3-return-review');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');H='79e7c63a6bfa5f002663924f5c7d4e72db705026'
paths=['TCSlib/Complexity/ClassNP/SAT.lean','TCSlib/Complexity/CookLevin/Hardness.lean','TCSlib/Complexity/ClassNP/Tautology.lean','TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean','TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean']
patterns={'canonical':'runFrom_state_ne_none_of_le','halt_absorb':'runFrom_of_halt','run_add':'runFrom_add','time_split':r'Nat\.(?:add_sub_of_le|exists_eq_add_of_le)|exists_eq_add','contrapositive':r'contrapose|by_contra','liveness':r'live_prefix|\.Halted|state\s*≠\s*none|state\s*=\s*none','least_time':r'Nat\.find|lt_trichotomy'}
allrows=[];overview=[]
for path in paths:
 raw=subprocess.check_output(['git','show',H+':'+path],cwd=R);text=raw.decode();q=P/'source79'/(path+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
 lines=text.splitlines();decl=[];depth=0
 for i,line in enumerate(lines,1):
  old=depth;j=0
  while j<len(line):
   if line.startswith('/-',j):depth+=1;j+=2
   elif line.startswith('-/',j)and depth:depth-=1;j+=2
   elif depth==0 and line.startswith('--',j):break
   else:j+=1
  if old:continue
  m=re.match(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:lemma|theorem|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)',line)
  if m:decl.append((i,m[1]))
 decl.append((len(lines)+1,'<end>'))
 picked=[]
 for (start,name),(end,_)in zip(decl,decl[1:]):
  chunk='\n'.join(lines[start-1:end-1]);hits={k:[start+i for i,l in enumerate(lines[start-1:end-1])if re.search(pat,l)]for k,pat in patterns.items()};hits={k:v for k,v in hits.items()if v}
  # Keep every absorption/canonical/time-split root, plus explicit live-prefix and
  # contraposition roots with live/halt conclusions; no closing syntax is a required filter.
  chosen=any(k in hits for k in ['canonical','halt_absorb','run_add','time_split','liveness'])
  if not chosen:continue
  row={'path':path,'declaration':name,'start_line':start,'end_line':end-1,'sha256':hashlib.sha256(chunk.encode()).hexdigest(),'hits':hits,'chunk':chunk};allrows.append(row);picked.append(name)
  print(path.split('/')[-1],name,start,end-1,','.join(f'{k}:{len(v)}'for k,v in hits.items()))
 overview.append({'path':path,'source':H,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'enumerated_declarations':len(decl)-1,'candidate_declarations':picked})
(P/'live-prefix-candidates.json').write_text(json.dumps({'source':H,'scope':'all five touched files; bounded candidate enumeration plus inspection, not a global absence claim','patterns':patterns,'files':overview,'candidates':allrows},indent=2,ensure_ascii=False)+'\n')
print('candidates',len(allrows))
