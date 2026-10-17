"""Compare declarations at their old home (before) with their new home (after).
usage: python3 -I moved.py <old-home-before> <new-home-after> <name,name,...>
For each name: statement (exact), docstring (exact), body (exact), with unified diffs of
whatever differs, and the citation-tag sets.
"""
import difflib, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from freeze2 import parse, tags

a, b = parse(sys.argv[1]), parse(sys.argv[2])
for n in sys.argv[3].split(','):
    x, y = a[n], b[n]
    print(f'===== {n}: old line {x["line"]}, new line {y["line"]}')
    for part in ('stmt', 'doc', 'body'):
        same = x[part] == y[part]
        print(f'  {part:4}: {"BYTE-IDENTICAL" if same else "DIFFERS"}')
    print(f'  sorry: {x["sorry"]} -> {y["sorry"]}')
    print(f'  tags before: {tags(x["doc"])}')
    print(f'  tags after:  {tags(y["doc"])}')
    for part in ('stmt', 'doc', 'body'):
        if x[part] != y[part]:
            print(f'  --- {part} diff:')
            sys.stdout.writelines('    ' + l for l in difflib.unified_diff(
                (x[part] + '\n').splitlines(True), (y[part] + '\n').splitlines(True),
                f'old/{n}.{part}', f'new/{n}.{part}'))
