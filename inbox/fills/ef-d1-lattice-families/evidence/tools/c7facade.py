"""c7facade.py <repo> <base> <head>: compare TCSlib/Cryptography/SIS.lean at base and head line by
line; allow exactly the two listed insertions; report every other difference. Control: the same
comparison with one character of the head copy altered must report exactly one difference."""
import subprocess, sys, difflib
repo, base, head = sys.argv[1:4]
F = 'TCSlib/Cryptography/SIS.lean'
ALLOWED = ['import TCSlib.Cryptography.SIS.Efficient',
           '* `Efficient`: efficient families (a uniform parameter map), dyadic schedules, non-vacuity.']
show = lambda r: subprocess.run(['git', '-C', repo, 'show', f'{r}:{F}'], capture_output=True, text=True).stdout.split('\n')
def diffs(a, b):
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes():
        if tag == 'equal': continue
        if tag == 'insert' and all(x in ALLOWED for x in b[j1:j2]): continue
        out.append((tag, a[i1:i2], b[j1:j2]))
    return out
a, b = show(base), show(head)
d = diffs(a, b)
ins = [x for x in b if x not in a]
print('inserted lines:', ins)
print('unexpected differences:', len(d), d)
b2 = list(b); k = next(i for i, x in enumerate(b2) if x.startswith('* `Assumption`'))
b2[k] = b2[k].replace('NUPPT', 'NUPPU', 1)
d2 = diffs(a, b2)
print('control (one character altered): differences =', len(d2), '->', 'PASS' if len(d2) == 1 else 'FAIL')
print('C7', 'PASS' if not d and sorted(ins) == sorted(ALLOWED) and len(d2) == 1 else 'FAIL')
