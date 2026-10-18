"""Print the statement (header up to the first top-level `:=`) of named declarations. Read-only.
Usage: python3 -I showstmt.py <file.lean> <name> [<name> ...]"""
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
        out = []
        for i in range(d['line'] - 1, d['end']):
            out.append(lines[i])
            if ':= by' in lines[i] or lines[i].rstrip().endswith(':=') or ' where' in lines[i]:
                break
        print(f'=== {nm} ({os.path.basename(path)}:{d["line"]}-{d["end"]})')
        print('\n'.join(out))
