"""Compare the completed final sweep's warnings with the issued admission inventory.
Run as python3 -I evidence/tools/check_admissions.py after all sweep modules pass.
"""
from pathlib import Path
import json,re
base={}
for line in Path('evidence/inputs/base-sorries.txt').read_text().splitlines():
 if line.startswith('TOTAL'):continue
 module,count,names=line.split(': ',2)
 if not module.startswith('TCSlib/'):module='TCSlib/Complexity/'+module
 for name in names.split(', '):base[(module,name)]=True
results=[json.loads(line) for line in Path('evidence/logs/final-sweep-results.jsonl').read_text().splitlines()]
order=Path('evidence/logs/final-sweep-order.txt').read_text().splitlines()
assert len(results)==len(order) and all(r['exit']==0 for r in results),'complete successful sweep required'
actual={}
pattern=re.compile(r'^(TCSlib/[^:]+)\.lean:(\d+):\d+: warning: declaration uses \'sorry\'',re.M)
decl=re.compile(r'^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|instance)\s+([^\s(:]+)')
for result in results:
 text=Path(result['log']).read_text()
 for match in pattern.finditer(text):
  module,number=match[1],int(match[2]);lines=Path(module+'.lean').read_text().splitlines()
  name=None
  for line in reversed(lines[:number]):
   d=decl.match(line)
   if d:name=d[1];break
  assert name,(module,number)
  pair=(module,name)
  assert pair not in actual,pair
  actual[pair]={'module':module,'name':name,'line':number,'log':result['log']}
target=('TCSlib/Cryptography/Randomness/Extraction','not_isExtractor_effSources')
removed=sorted(set(base)-set(actual));added=sorted(set(actual)-set(base))
report={'base_declarations':len(base),'final_declarations':len(actual),'base_modules':len({p[0] for p in base}),'final_modules':len({p[0] for p in actual}),'removed':removed,'added':added,'actual':list(actual.values()),'pass':removed==[target] and not added}
Path('evidence/logs/admissions-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='actual'},indent=2))
assert report['pass']
