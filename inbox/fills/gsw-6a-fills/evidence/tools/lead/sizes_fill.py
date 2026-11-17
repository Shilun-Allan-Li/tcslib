"""sizes_fill.py <repo> <base> <head> (gsw-6a-fills, new; check 8): lines and maximal width (Python len) of the six
owned files at <base> and <head> (git show), the fill delta, the r3 §H7 estimate per unit, and the limits (every
line <= 100, every file <= 1000 lines)."""
import sys, subprocess
repo, base, head = sys.argv[1:4]
F = [('U4', 'TCSlib/Complexity/BranchingPrograms/BarringtonConverse.lean', '250-400'),
     ('U5', 'TCSlib/Complexity/BranchingPrograms/NC1.lean', '180-320'),
     ('U7', 'TCSlib/Complexity/CircuitComplexity/NANDLayering.lean', '150-250 (up to ~300)'),
     ('U9', 'TCSlib/Complexity/CircuitComplexity/FormulaArith/CarrySave.lean', '250-400'),
     ('U10', 'TCSlib/Complexity/CircuitComplexity/FormulaArith/Compare.lean', '150-250'),
     ('U11', 'TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean', '150-250')]
def show(rev, f): return subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, check=True).stdout.decode()
bad = 0; tot = 0
print('unit\tfile\tbase_lines\thead_lines\tdelta\tr3_estimate\tbase_maxwidth\thead_maxwidth\tdiff_added\tdiff_removed')
for u, f, est in F:
    b, h = show(base, f).split('\n'), show(head, f).split('\n')
    if b[-1] == '': b = b[:-1]
    if h[-1] == '': h = h[:-1]
    st = subprocess.run(['git', '-C', repo, 'diff', '--numstat', base, head, '--', f], capture_output=True, text=True).stdout.split()
    mb, mh = max(map(len, b)), max(map(len, h))
    bad += mh > 100 or len(h) > 1000
    tot += len(h) - len(b)
    print(f'{u}\t{f}\t{len(b)}\t{len(h)}\t{len(h) - len(b)}\t{est}\t{mb}\t{mh}\t{st[0] if st else 0}\t{st[1] if st else 0}')
print(f'RESULT total_delta={tot} limit_violations={bad}')
