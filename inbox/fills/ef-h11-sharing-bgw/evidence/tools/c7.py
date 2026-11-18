"""c7.py <repo> <base> <head> <file> <allowed.txt>: compare a facade at base and head line by line;
only the listed inserted lines are allowed; nothing removed or changed. Prints differences."""
import sys, subprocess, difflib
repo, base, head, f, allowed = sys.argv[1:6]
def show(r, p=None):
    if p: return open(p, encoding='utf-8').read().split('\n')
    return subprocess.run(['git','-C',repo,'show',f'{r}:{f}'],capture_output=True,text=True).stdout.split('\n')
a = show(base); b = show(head, sys.argv[6] if len(sys.argv) > 6 else None)
ok = [l.rstrip('\n') for l in open(allowed, encoding='utf-8')]
diffs = []
for op, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
    if op == 'equal': continue
    if op == 'insert' and all(l in ok for l in b[j1:j2]): continue
    diffs.append((op, a[i1:i2], b[j1:j2]))
for d in diffs: print('DIFF', d)
print(f, 'differences:', len(diffs))
