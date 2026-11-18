from pathlib import Path
import csv,json,re,subprocess
out=Path(__file__).resolve().parent
meta=json.loads((out/'source-snapshot.json').read_text());head=meta['candidate']
rows=list(csv.DictReader((out/'fidelity-declarations.tsv').open(),delimiter='\t'));groups={}
for row in rows:
 p,n=row['file_line'].rsplit(':',1);groups.setdefault(p,[]).append((int(n),row))
plan=[]
for p,items in groups.items():
 s=subprocess.check_output(['git','show',head+':'+p],text=True);lines=s.splitlines()
 for idx,(line,row) in enumerate(items):
  stop=items[idx+1][0]-1 if idx+1<len(items) else len(lines)
  body='\n'.join(lines[line-1:stop]);body=re.sub(r'/-[\s\S]*?-/', '',body)
  body=re.sub(r'--[^\n]*','',body)
  if not re.search(r'\bsorry\b',body):continue
  prefix='\n'.join(lines[:line-1]);docs=list(re.finditer(r'/--([\s\S]*?)-/',prefix))
  doc=docs[-1][1] if docs else ''
  sketch=doc.split('**Proof sketch.**',1)[-1].strip() if '**Proof sketch.**' in doc else 'MISSING SKETCH'
  if '/Targets.' in p:phase='M6'
  elif '/Security.' in p:phase='M4' if row['Lean_name'].split('.')[-1] in ['prop41','lemma42'] else 'M5'
  elif '/Stretch.' in p:phase='M2'
  elif '/Claim42' in p:phase='M3'
  elif '/Reductions/' in p:phase='M4 / M6'
  elif '/Hybrids.' in p:phase='M4'
  elif '/Encoding.' in p:phase='M6 / supporting M1-M3'
  else:phase='M1 / foundational glue'
  plan.append([row['Lean_name'],row['file_line'],phase,' '.join(sketch.split())])
with (out/'proof-obligations.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n')
 w.writerow(['Lean_name','file_line','milestone','owner_proof_sketch']);w.writerows(plan)
print('Named M0 obligations:',len(plan))
print('Missing sketches:',sum(p[-1]=='MISSING SKETCH' for p in plan))
