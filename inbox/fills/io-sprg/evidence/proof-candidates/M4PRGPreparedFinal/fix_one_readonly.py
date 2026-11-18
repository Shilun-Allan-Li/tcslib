from pathlib import Path
import difflib,hashlib,json,re,sys
base=Path('/private/tmp/io-sprg-proof-notes')
relative=sys.argv[1];src=base/relative;raw=src.read_text();lines=raw.splitlines(keepends=True);changes=[]
for i in range(len(lines)-1,-1,-1):
 m=re.match(r'( *)(?:(·) )?have\s+.*?:',lines[i])
 if not m or ':=' in lines[i]:continue
 indent=m.group(1)+('  ' if m.group(2) else '');j=i+1
 while j<len(lines) and not lines[j].startswith(indent+'·'):
  if re.match(re.escape(indent)+r'(?:have|intro|rw|exact|apply|refine|calc|obtain|rcases|by_cases|simp|change|let|filter_upwards|constructor|positivity|omega|nlinarith)\b',lines[j]):break
  j+=1
 if j==len(lines) or not lines[j].startswith(indent+'·') or ':=' in ''.join(lines[i:j]):continue
 k=j-1
 while not lines[k].strip():k-=1
 lines[k]=lines[k].rstrip('\n')+' := ?_\n';lines.insert(j,indent+'swap\n')
 changes.append({'kind':'typed-have','original_line':i+1,'bullet_prefix':bool(m.group(2))})
s=''.join(lines)
if relative.endswith('04-prg_verdict_prob.proposed.lean'):
 old='(uprob_comp_equiv (NUPPT.coinsEquivPoly hB.coins_eq N).symm _).symm'
 new='''(uprob_comp_equiv (NUPPT.coinsEquivPoly hB.coins_eq N).symm
          (fun r : B.Coins N => B.distinguisherL N (P.prgEnc N x) r = true)).symm'''
 assert old in s;s=s.replace(old,new)
 changes.append({'kind':'typed-uprob-reindex-event','detail':'Explicit target coin predicate, no higher-order event placeholder'})
 old='rw [Bridge.prob_sample_eq_uprob, Bridge.prob_sample_eq_uprob]'
 new='''rw [Bridge.prob_sample_eq_uprob
      (fun r : B.Coins N => B.distinguisherL N (P.prgEnc N x) r = true),
    Bridge.prob_sample_eq_uprob
      (fun r : A.Coins (P.kappaOfN N) =>
        A.distinguisherL (P.kappaOfN N) (P.prgPre π N (ω N) x) r = true)]'''
 assert old in s;s=s.replace(old,new)
 changes.append({'kind':'typed-probability-bridges','detail':'Explicit two actual coin types and full event functions'})
code=re.sub(r'/\-.*?\-/','',s,flags=re.S);code=re.sub(r'--[^\n]*','',code)
assert len(re.findall(r'\bby\b',code))==1
assert not re.search(r'\b(sorry|admit)\b',code)
assert max(map(len,s.splitlines()))<=100
out=base/'M4PRGPrepared/candidates'/relative;out.parent.mkdir(parents=True,exist_ok=True);out.write_text(s)
binding={'original':str(src),'original_sha256':hashlib.sha256(raw.encode()).hexdigest(),
 'candidate':str(out),'candidate_sha256':hashlib.sha256(s.encode()).hexdigest(),
 'changes':list(reversed(changes)),'status':'UNRUN_NO_LEAN'}
out.with_name(out.name+'.binding.json').write_text(json.dumps(binding,indent=2)+'\n')
out.with_name(out.name+'.diff').write_text(''.join(difflib.unified_diff(raw.splitlines(keepends=True),s.splitlines(keepends=True),fromfile=str(src),tofile=str(out))))
print(str(out),len(changes),'changes')
