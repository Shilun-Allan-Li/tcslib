#!/usr/bin/env python3
"""Compute the exact dependency closure and direct Mathlib roots of approved extra imports."""
import json
from pathlib import Path
import re

new_roots = ['TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines',
             'TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/ReductionMachine']
old = Path('evidence/inputs/order.txt').read_text().splitlines()
seen = set(old)
added = []
all_math = set(Path('evidence/logs/mathlib-roots.txt').read_text().splitlines())
math = set()
active = set()

def visit(module):
    if module in seen:
        return
    if module in active:
        raise RuntimeError('Import cycle ' + module)
    active.add(module)
    source = Path(module + '.lean').read_text()
    for imported in re.findall(r'^import ([^\s]+)', source, re.M):
        if imported.startswith('TCSlib.'):
            visit(imported.replace('.', '/'))
        elif imported.startswith('Mathlib.'):
            math.add(imported)
    active.remove(module)
    seen.add(module)
    added.append(module)
for module in new_roots:
    visit(module)
Path('evidence/inputs/extra-order.txt').write_text(''.join(m + '\n' for m in added))
Path('evidence/logs/extra-mathlib-roots.txt').write_text(''.join(m + '\n' for m in sorted(math-all_math)))
Path('evidence/inputs/extended-order.txt').write_text(''.join(m + '\n' for m in old+added))
print(json.dumps(dict(new_modules=added, new_mathlib_roots=sorted(math-all_math)), indent=2))
