"""Line widths (Python len, at most 100) and file sizes (at most 1000 lines) (python3 -I).
Usage: widths.py <file> [<file> ...]   Exit 0 iff every line is <= 100 and every file <= 1000."""
import sys
bad = 0
for f in sys.argv[1:]:
    lines = open(f, encoding='utf-8').read().split('\n')
    n = len(lines) - (lines[-1] == '')
    over = [(i, len(l)) for i, l in enumerate(lines, 1) if len(l) > 100]
    print(f'{f}: {n} lines, max width {max(map(len, lines))}, over-100 lines {len(over)}')
    for i, w in over:
        print(f'  line {i}: {w}')
    bad += bool(over) or n > 1000
print('WIDTHS ' + ('PASS' if not bad else 'FAIL'))
sys.exit(1 if bad else 0)
