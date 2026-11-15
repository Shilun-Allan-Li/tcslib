#!/usr/bin/env python3
"""Line widths (Python len) and line counts of the changed and new files.
usage: widths.py ROOT FILE..."""
import sys, os
root = sys.argv[1]; bad = 0
for f in sys.argv[2:]:
    lines = open(os.path.join(root, f), encoding='utf-8').read().split('\n')
    if lines and lines[-1] == '': lines = lines[:-1]
    over = [(i + 1, len(l)) for i, l in enumerate(lines) if len(l) > 100]
    print(f'{f}: {len(lines)} lines, max width {max((len(l) for l in lines), default=0)}, '
          f'{len(over)} over 100' + ('' if len(lines) <= 1000 else ' FILE OVER 1000 LINES'))
    for i, w in over: print(f'  OVER {f}:{i} width {w}')
    bad += len(over) + (len(lines) > 1000)
print('RESULT', 'OK' if bad == 0 else f'{bad} violations')
