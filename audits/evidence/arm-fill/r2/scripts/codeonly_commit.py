"""Is a commit's change to its .lean files comment-only? Compares the comment-stripped text of
each changed .lean file at the first parent and at the commit (files given as two local copies).
usage: python3 -I codeonly_commit.py <before> <after> [<before> <after> ...]"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leancore import strip_keep_lines
a = sys.argv[1:]; same = 0
for i in range(0, len(a), 2):
    x = strip_keep_lines(open(a[i], encoding='utf-8').read()) if os.path.getsize(a[i]) else ''
    y = strip_keep_lines(open(a[i + 1], encoding='utf-8').read())
    norm = lambda t: '\n'.join(l.rstrip() for l in t.split('\n') if l.strip())
    ok = norm(x) == norm(y); same += ok
    if not ok: print('CODE DIFFERS:', a[i + 1])
print(f'{same} of {len(a)//2} changed .lean files are comment-only changes (blank lines ignored)')
