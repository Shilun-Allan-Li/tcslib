"""downstream.py <repo> <rev> <closure-file> <changed-module>: modules of the closure (in order) that import the changed module transitively, including it."""
import sys, subprocess, re
repo, rev, cl, ch = sys.argv[1:]
order = open(cl).read().split()
imps = {}
for m in order:
    s = subprocess.run(['git','-C',repo,'show',f'{rev}:'+m.replace('.','/')+'.lean'],capture_output=True,text=True).stdout
    imps[m] = [i for i in re.findall(r'^import\s+(\S+)', s, re.M)]
down = {ch}
for m in order:
    if any(i in down for i in imps[m]): down.add(m)
for m in order:
    if m in down: print(m)
