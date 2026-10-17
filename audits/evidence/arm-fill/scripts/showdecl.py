"""Print the statements (and optionally docstrings) of named declarations of a file.
usage: python3 -I showdecl.py <file> <name,name,...> [--doc]
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from freeze2 import parse
ds = parse(sys.argv[1])
for n in sys.argv[2].split(','):
    if n not in ds: print(f'-- {n}: NOT FOUND'); continue
    d = ds[n]
    print(f'-- {n} (line {d["line"]}, {d["kind"]}{", private" if d["private"] else ""}, body {len([l for l in d["body"].splitlines() if l.strip()])} lines)')
    if '--doc' in sys.argv: print(d['doc'])
    print(d['stmt'])
    if d['kind'] in ('def', 'abbrev', 'structure', 'inductive') and '--body' in sys.argv: print(d['body'][:3000])
    print()
