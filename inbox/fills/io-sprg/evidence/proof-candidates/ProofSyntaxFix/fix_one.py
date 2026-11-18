from pathlib import Path
import re, sys, json, hashlib
base=Path('/private/tmp/io-sprg-proof-notes')
rel=sys.argv[1]
src=base/rel
raw=src.read_bytes()
s=raw.decode()
lines=s.splitlines(keepends=True)
fixes=[]
for i in range(len(lines)-1,-1,-1):
 m=re.match(r'( *)have\s+.*?:',lines[i])
 if not m or ':=' in lines[i]: continue
 indent=m.group(1)
 j=i+1
 while j<len(lines) and not lines[j].startswith(indent+'·'):
  if lines[j].strip() and len(lines[j])-len(lines[j].lstrip())<=len(indent): break
  j+=1
 if j==len(lines) or not lines[j].startswith(indent+'·'): continue
 if ':=' in ''.join(lines[i:j]): continue
 k=j-1
 while not lines[k].strip(): k-=1
 lines[k]=lines[k].rstrip('\n')+' := ?_\n'
 lines.insert(j,indent+'swap\n')
 fixes.append({'kind':'typed-have','original_line':i+1})
s=''.join(lines)
if rel=='LPNRawEncoding/01-encDraw_injective.proof':
 old='(ih ys (congrArg Prod.snd hp))'
 assert old in s
 s=s.replace(old,'(ih (congrArg Prod.snd hp))')
 fixes.append({'kind':'implicit-IH-binder','detail':'remove explicit ys; implicit Function.Injective second argument'})
if rel.endswith('.term.txt'):
 s='by\n  exact '+s[s.index('sparseFactor_mul M t'):].strip()+'\n'
 fixes.append({'kind':'term-to-outer-by'})
code=re.sub(r'/\-.*?\-/', '', s, flags=re.S)
code=re.sub(r'--[^\n]*', '', code)
assert len(re.findall(r'\bby\b',code))==1,(rel,'outer-by-count')
out=base/'ProofSyntaxFix'/rel
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(s)
meta={'source':str(src),'source_sha256':hashlib.sha256(raw).hexdigest(),
      'candidate':str(out),'candidate_sha256':hashlib.sha256(s.encode()).hexdigest(),
      'changes':list(reversed(fixes)),'outer_by':1,'untested':True}
out.with_name(out.name+'.binding.json').write_text(json.dumps(meta,indent=2)+'\n')
print(str(out),json.dumps(meta['changes']))
