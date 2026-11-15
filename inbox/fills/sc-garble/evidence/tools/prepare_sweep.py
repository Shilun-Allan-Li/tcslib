#!/usr/bin/env python3
"""Insert all permitted helpers and order actual TCSlib imports topologically."""
import json
from pathlib import Path
import re
import subprocess
base='fbd37f447596d4207c8d08b7ef7602f57fe95198'
issued=Path('evidence/issued/order.txt').read_text().splitlines()
issued=[m for m in issued if m.strip()]
source=Path('evidence/source-files.txt').read_text().splitlines()
new=[]
for file in source:
 r=subprocess.run(['git','cat-file','-e',base+':'+file],capture_output=True)
 if r.returncode:new.append(file[:-5])
universe=set(issued+new)
seen=set();active=set();order=[];deps={}
def visit(m):
 if m in seen:return
 assert m not in active,('import cycle',m)
 active.add(m)
 p=Path(m+'.lean')
 imports=[x.replace('.','/')for x in re.findall(r'^import (TCSlib\.[^\s]+)',p.read_text(),re.M)]
 deps[m]=imports
 for d in imports:
  assert d in universe,('new TCSlib import outside issued closure',m,d)
  visit(d)
 active.remove(m);seen.add(m);order.append(m)
for m in issued+new:visit(m)
assert len(issued)==166 and len(new)==8 and len(order)==174
Path('evidence/final-order.txt').write_text(''.join(m+'\n'for m in order))
Path('evidence/final-import-graph.json').write_text(json.dumps(deps,indent=2)+'\n')
print('ORDER PASS: 166 issued + 8 helpers = 174 modules; acyclic and closed')
