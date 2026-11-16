"""Print, in order.txt order, the TCSlib modules of the order list that the given
modules import directly or indirectly (the given modules themselves excluded).
Usage: closure.py <order.txt> <module> [<module> ...]   (run from the checkout root)"""
import re, sys
from pathlib import Path
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
def imports(m):
    src = Path(m + '.lean').read_text()
    return [x.replace('.', '/') for x in re.findall(r'^import (TCSlib\S*)', src, re.M)]
seen, stack = set(), list(sys.argv[2:])
while stack:
    for i in imports(stack.pop()):
        if i not in seen:
            seen.add(i); stack.append(i)
missing = seen - set(order)
assert not missing, missing
for m in order:
    if m in seen and m not in sys.argv[2:]:
        print(m)
