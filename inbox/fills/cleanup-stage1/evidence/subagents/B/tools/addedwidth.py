"""List added lines (git diff of the worktree) longer than 100 characters."""
import subprocess, sys
d = subprocess.run(['git', '-C', sys.argv[1], 'diff', '-U0'], capture_output=True, text=True).stdout
f = None; n = 0; bad = 0
for l in d.split('\n'):
    if l.startswith('+++ '): f = l[6:]
    elif l.startswith('@@'):
        n = int(l.split('+')[1].split(',')[0].split(' ')[0])
    elif l.startswith('+'):
        if len(l) - 1 > 100: print(f, n, len(l) - 1); bad += 1
        n += 1
print('over100:', bad)
