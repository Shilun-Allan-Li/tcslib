#!/usr/bin/env python3
"""Insert the actual helper import closure before consumers in the narrowed issued order."""
from pathlib import Path
import re,json
roots=Path('evidence/inputs/extended-order-v3.txt').read_text().splitlines()
seen=set();active=set();order=[]
def visit(module):
 if module in seen:return
 assert module not in active,module
 active.add(module)
 for imp in re.findall(r'^import ([^\s]+)',Path(module+'.lean').read_text(),re.M):
  if imp.startswith('TCSlib.'):visit(imp.replace('.','/'))
 active.remove(module);seen.add(module);order.append(module)
for root in roots:visit(root)
extra=set(order)-set(roots)
assert all(m.startswith('TCSlib/Cryptography/SecureComputation/Yao/') for m in extra),sorted(extra)
Path('evidence/inputs/checkpoint3-sweep-order.txt').write_text(''.join(m+'\n' for m in order))
print(json.dumps(dict(modules=len(order),inserted_helpers=sorted(extra)),indent=2))
