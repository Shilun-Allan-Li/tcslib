#!/usr/bin/env python3
"""Exact closure for the third approved, published-interface import."""
import json
from pathlib import Path
import re
old=Path('evidence/inputs/extended-order.txt').read_text().splitlines()
seen=set(old);added=[];math=set()
known=set(Path('evidence/logs/mathlib-roots.txt').read_text().splitlines())
known.update(Path('evidence/logs/extra-mathlib-roots.txt').read_text().splitlines())
def visit(m):
    if m in seen:return
    seen.add(m)
    for imp in re.findall(r'^import ([^\s]+)',Path(m+'.lean').read_text(),re.M):
        if imp.startswith('TCSlib.'):visit(imp.replace('.','/'))
        elif imp.startswith('Mathlib.'):math.add(imp)
    added.append(m)
visit('TCSlib/Cryptography/Encryption/PrivateKey/FromPRF/HybridLemmas')
Path('evidence/inputs/probability-order.txt').write_text(''.join(m+'\n' for m in added))
Path('evidence/inputs/extended-order-v2.txt').write_text(''.join(m+'\n' for m in old+added))
Path('evidence/logs/probability-mathlib-roots.txt').write_text(''.join(m+'\n' for m in sorted(math-known)))
print(json.dumps(dict(new_modules=added,new_mathlib_roots=sorted(math-known)),indent=2))
