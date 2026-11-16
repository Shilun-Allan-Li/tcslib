#!/usr/bin/env python3
"""Write a fresh topological issued-plus-approved order, including every helper."""
import argparse
import json
from pathlib import Path
import re

p = argparse.ArgumentParser()
p.add_argument('--output', required=True)
a = p.parse_args()
roots = Path('evidence/inputs/extended-order-v3.txt').read_text().splitlines()
seen, active, order = set(), set(), []

def visit(module):
    if module in seen:
        return
    assert module not in active, module
    active.add(module)
    for imp in re.findall(r'^import ([^\s]+)', Path(module + '.lean').read_text(), re.M):
        if imp.startswith('TCSlib.'):
            visit(imp.replace('.', '/'))
    active.remove(module)
    seen.add(module)
    order.append(module)

for root in roots:
    visit(root)
extra = set(order) - set(roots)
assert all(m.startswith('TCSlib/Cryptography/SecureComputation/Yao/') for m in extra)
helpers = {str(p.with_suffix('')) for p in
           Path('TCSlib/Cryptography/SecureComputation/Yao').rglob('*.lean')}
assert helpers <= set(order), helpers - set(order)
out = Path(a.output)
assert not out.exists(), out
out.write_text(''.join(m + '\n' for m in order))
print(json.dumps(dict(modules=len(order), approved_modules=len(roots),
                      inserted_helpers=sorted(extra)), indent=2))
