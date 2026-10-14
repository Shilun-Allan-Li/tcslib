"""Print declarations (with their docstrings) of a Lean file by name. Read-only.
Usage: python3 -I showdecl.py <file.lean> <name> [<name> ...]"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decls import scan
path = sys.argv[1]
ds, lines = scan(path)
for nm in sys.argv[2:]:
    hit = [d for d in ds if d['name'] == nm]
    if not hit:
        print(f'=== {nm}: NOT FOUND'); continue
    for d in hit:
        s = d['line'] - 1
        # back up over docstring
        j = s - 1
        while j >= 0 and lines[j].strip() == '':
            j -= 1
        if j >= 0 and lines[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and not lines[k].lstrip().startswith('/--'):
                k -= 1
            s = k
        print(f'=== {nm} ({os.path.basename(path)}:{d["line"]}-{d["end"]})')
        print('\n'.join(lines[s:d['end']]))
