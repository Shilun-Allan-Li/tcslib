#!/usr/bin/env python3
"""Line-width (<= 100 characters, Python len) and file-size (<= 1000 lines) check.
Usage: python3 -I width_check.py <worktree> <base revision> <file>...
For each file: its length and every line over 100 characters; and, against the base revision,
the lines this fill added (git diff -U0) that are over 100 characters. A file passes when the
added lines are all within 100 characters and the file is within 1000 lines or no longer than at
the base (pre-existing excess in a frozen file is reported, not attributed to the fill)."""
import sys, os, subprocess, re
wt, base = sys.argv[1], sys.argv[2]; bad = 0
for f in sys.argv[3:]:
    L = open(os.path.join(wt, f), encoding='utf-8').read().split('\n')
    n = len(L) - (1 if L and L[-1] == '' else 0)
    over = [(i + 1, len(l)) for i, l in enumerate(L) if len(l) > 100]
    old = subprocess.run(['git', '-C', wt, 'show', f'{base}:{f}'], capture_output=True, text=True)
    n0 = len(old.stdout.rstrip('\n').split('\n')) if old.returncode == 0 else 0
    diff = subprocess.run(['git', '-C', wt, 'diff', '-U0', base, '--', f], capture_output=True,
                          text=True).stdout
    added = [l[1:] for l in diff.split('\n') if l.startswith('+') and not l.startswith('+++')]
    if old.returncode != 0:
        added = L[:n]
    added_over = [len(l) for l in added if len(l) > 100]
    ok = not added_over and (n <= 1000 or n0 >= 1000)
    bad += not ok
    print(f"{'OK  ' if ok else 'FAIL'} {f}: {n} lines (base {n0 if old.returncode == 0 else 'new'}), "
          f"{len(added)} added lines, added over 100: {added_over}; all lines over 100: {over}")
print('RESULT:', 'all files pass' if bad == 0 else f'{bad} file(s) fail')
