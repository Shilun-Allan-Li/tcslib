from pathlib import Path
import sys,re,json,hashlib,difflib
base=Path('/private/tmp/io-sprg-proof-notes');rel=sys.argv[1];src=base/rel;raw=src.read_bytes();s=raw.decode();lines=s.splitlines(keepends=True);changes=[]
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
 lines[k]=lines[k].rstrip('\n')+' := ?_\n';lines.insert(j,indent+'swap\n');changes.append({'kind':'typed-have','line':i+1,'bullet_prefix':bool(m.group(2))})
s=''.join(lines)
if rel.endswith('13-cond2_sparse_joint_le_quarter_pow.lean.candidate'):
 old='← Games.Bridge.expect_sample_pair]'
 new='← Games.Bridge.expect_sample_pair\n      (fun z : P.IdDraw κ pp × D => if event z then (1 : ℝ) else 0)]'
 assert old in s;s=s.replace(old,new);changes.append({'kind':'explicit-uniform-pair-reader-argument','detail':'Pin actual IdDraw x Draw and event indicator; prevents rw selecting a marginal product sample.'})
code=re.sub(r'/\-.*?\-/','',s,flags=re.S);code=re.sub(r'--[^\n]*','',code);assert len(re.findall(r'\bby\b',code))==1
out=base/'M3Prepared/candidates'/rel;out.parent.mkdir(parents=True,exist_ok=True);out.write_text(s)
binding={'original':str(src),'original_sha256':hashlib.sha256(raw).hexdigest(),'candidate':str(out),'candidate_sha256':hashlib.sha256(s.encode()).hexdigest(),'changes':list(reversed(changes)),'status':'UNRUN'}
out.with_name(out.name+'.binding.json').write_text(json.dumps(binding,indent=2)+'\n');out.with_name(out.name+'.diff').write_text(''.join(difflib.unified_diff(raw.decode().splitlines(keepends=True),s.splitlines(keepends=True),fromfile=str(src),tofile=str(out))))
print(str(out),len(changes))
