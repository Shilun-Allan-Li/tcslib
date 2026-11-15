#!/usr/bin/env python3
"""Inventory explicit proof rewrite/unfold arguments against the sealed TCSlib definitions."""
import importlib.util
import json
from pathlib import Path
import re
spec=importlib.util.spec_from_file_location('headers','evidence/tools/check_headers.py')
h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
spec2=importlib.util.spec_from_file_location('unfold_args','evidence/tools/unfold_arguments.py')
u=importlib.util.module_from_spec(spec2);spec2.loader.exec_module(u)
manifest=json.loads(Path('evidence/seals/final/manifest.json').read_text())
records=[];violations=[]
lookup={}
for path in sorted(Path('evidence/logs').glob('seals-final*/results.jsonl')):
 lookup.update({r['module']:r for r in map(json.loads,path.read_text().splitlines())})
for row in manifest:
 if row.get('variant')!='A'or row.get('coercions')!='coe':continue
 source=Path(row['probe']).read_text().splitlines(True)
 i=row['original_insert_line'];k=row['inserted_lines']
 source=''.join(source[:i]+source[i+k:])
 code,_=h.lex(source)
 if row['probe'][:-5]not in lookup:continue
 logfile=Path(lookup[row['probe'][:-5]]['log'])
 foreign=[]
 for line in logfile.read_text().splitlines():
  if line.startswith('SEALED\t')or line.startswith('EXCLUDED\t'):
   status,home,name=line.split('\t',2)
   foreign.append((name,home,status))
 byshort={}
 for name,home,status in foreign:
  byshort.setdefault(name.split('.')[-1],[]).append((name,home,status))
 for offset,tactic,token in u.arguments(code):
  for name,home,status in byshort.get(token.split('.')[-1],[]):
   if '.'in token and not name.endswith('.'+token)and name!=token:continue
   entry=dict(file=row['file'],line=code[:offset].count('\n')+1,tactic=tactic,
     argument=token,foreign_name=name,home=home,seal_status=status)
   records.append(entry)
   if status=='SEALED':violations.append(entry)
out=Path('evidence/unfold');out.mkdir(parents=True,exist_ok=True)
(out/'inventory.json').write_text(json.dumps(records,indent=2)+'\n')
(out/'potential-violations.json').write_text(json.dumps(violations,indent=2)+'\n')
print('Explicit rewrite/unfold arguments matching foreign definitions:',len(records))
print('Potential sealed-definition reads:',len(violations))
for row in violations:print(row)
print('This static suffix scan is conservative; any local-name ambiguity is reviewed manually.')
