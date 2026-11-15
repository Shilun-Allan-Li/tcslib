#!/usr/bin/env python3
"""Line-width (<= 100 characters, Python len) and file-size (<= 1000 lines) check of the changed and
new files. Usage: python3 -I width_check.py <worktree> <file>..."""
import sys, os
wt = sys.argv[1]; bad = 0
for f in sys.argv[2:]:
    L = open(os.path.join(wt, f), encoding='utf-8').read().split('\n')
    n = len(L) - (1 if L and L[-1] == '' else 0)
    over = [(i + 1, len(l)) for i, l in enumerate(L) if len(l) > 100]
    ok = n <= 1000 and not over
    bad += not ok
    print(f"{'OK  ' if ok else 'FAIL'} {f}: {n} lines, max width {max(len(l) for l in L)}, over 100: {over}")
print('RESULT:', 'all files pass' if bad == 0 else f'{bad} file(s) fail')
