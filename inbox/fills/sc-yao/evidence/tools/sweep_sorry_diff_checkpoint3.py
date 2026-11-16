#!/usr/bin/env python3
"""Validate every completed sweep module and compare warning declaration names to the issue."""
import json,re,runpy
from pathlib import Path
lex=runpy.run_path('evidence/tools/header_lexer.py')
order=Path('evidence/inputs/checkpoint3-sweep-order.txt').read_text().splitlines()
rows=[]
for phase in ['checkpoint3-sweep']:
 rows.extend(map(json.loads,(Path('evidence/logs')/phase/'results.jsonl').read_text().splitlines()))
assert len(rows)==len(order)==240
assert [r['module'] for r in rows]==order
warnings=[]
for row in rows:
 assert row['exit']==row['errors']==row['generic_errors']==0 and row['fresh_olean'],row
 source=Path(row['source']).read_text();ds=lex['declarations'](source);raw=Path(row['log']).read_text()
 for line in re.findall(r'^\S+\.lean:(\d+):\d+: warning: declaration uses \'sorry\'',raw,re.M):
  offset=sum(len(s)+1 for s in source.splitlines()[:int(line)-1]);d=next(d for d in ds if d['start']<=offset<d['end'])
  warnings.append(dict(module=row['module'],name=d['name'],line=int(line),log=row['log']))
actual={(r['module'],r['name']) for r in warnings};expected=set()
for line in Path('evidence/inputs/base-sorries.txt').read_text().splitlines():
 if line.startswith('TOTAL'):continue
 module,number,names=line.split(': ',2)
 if not module.startswith('TCSlib/'):module='TCSlib/Complexity/'+module
 for name in names.split(', '):expected.add((module,name))
removed=expected-actual;added=actual-expected
assert removed=={('TCSlib/Cryptography/SecureComputation/Yao','yaoHybrid_polyTime')},removed
assert not added,added
assert len(warnings)==31
summary=dict(modules=len(rows),errors=0,base_sorry_declarations=len(expected),current_sorry_declarations=len(actual),removed=sorted(removed),added=sorted(added),warnings=warnings)
Path('evidence/checkpoint3-sweep-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('240 MODULES PASS;31 SORRY DECLARATIONS; ONLY yaoHybrid_polyTime REMOVED')
