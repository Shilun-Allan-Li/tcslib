"""widths.py <root> <file>... (fill bb1-machine, Claude lead): line widths (Python len) and line counts;
prints every line over 100 characters and every file over 1000 lines, then a summary."""
import sys
root, files = sys.argv[1], sys.argv[2:]; bad = 0
for f in files:
    L = open(f'{root}/{f}', encoding='utf-8').read().split('\n')
    n = len(L) - (L[-1] == '')
    over = [(i, len(l)) for i, l in enumerate(L, 1) if len(l) > 100]
    for i, w in over: print(f'{f}:{i}: {w} > 100')
    if n > 1000: print(f'{f}: {n} lines > 1000')
    bad += len(over) + (n > 1000); print(f'{f}\t{n} lines\tmax width {max(map(len, L))}')
print('WIDTH/SIZE', 'PASS' if bad == 0 else 'FAIL', bad, 'violation(s)')
