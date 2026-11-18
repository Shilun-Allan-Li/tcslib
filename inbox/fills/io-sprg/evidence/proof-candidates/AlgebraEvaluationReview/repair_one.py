"""Repair one staged proof string only. Static text operation; never invokes Lean."""
from pathlib import Path
import csv,re,sys,hashlib,json
base=Path('/private/tmp/io-sprg-proof-notes/AlgebraEvaluation')
out=Path('/private/tmp/io-sprg-proof-notes/AlgebraEvaluationReview')
rows=list(csv.DictReader((base/'inventory.tsv').open(),delimiter='\t'))
row=next(r for r in rows if r['declaration']==sys.argv[1])
src=(base/row['candidate']).resolve()
lines=src.read_text().splitlines();fixes=[]
for i,line in enumerate(lines):
 m=re.match(r'^(\s*)have\s',line)
 if not m:continue
 n=len(m[1]);j=i+1
 while j<len(lines) and (not lines[j].strip() or len(lines[j])-len(lines[j].lstrip())>n):j+=1
 if j<len(lines) and re.match(r'^\s*·(?:\s|$)',lines[j]) and len(lines[j])-len(lines[j].lstrip())==n and ':=' not in '\n'.join(lines[i:j]):fixes.append((j-1,n))
for k,n in reversed(fixes):
 lines[k]+=' := ?_'
 lines.insert(k+1,' '*n+'swap')
text='\n'.join(lines)+'\n'
assert len(re.findall(r"(?<![\w'])by(?![\w'])",text))==1
assert not re.search(r'\bsorry\b',text)
assert max(map(len,lines))<=100
name=row['module']+'--'+row['declaration'].replace("'",'prime').replace('.','-')+'.proof'
dest=out/'corrected'/name;dest.parent.mkdir(exist_ok=True)
dest.write_text(text)
meta={'name':row['declaration'],'source':str(src),'output':str(dest),'repairs':len(fixes),'status':'NOT_RUN','sha256':hashlib.sha256(text.encode()).hexdigest()}
(dest.with_suffix('.json')).write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta))
