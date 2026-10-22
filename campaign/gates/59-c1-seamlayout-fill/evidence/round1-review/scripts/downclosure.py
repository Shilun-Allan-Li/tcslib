import subprocess, sys, re
W, rev = sys.argv[1], sys.argv[2]; roots = sys.argv[3:]
files=[f for f in subprocess.run(["git","-C",W,"ls-tree","-r","--name-only",rev,"--","TCSlib","TCSlib.lean"],capture_output=True,text=True).stdout.split() if f.endswith('.lean')]
mod=lambda f: f[:-5].replace('/','.')
imp={}
for f in files:
    src=subprocess.run(["git","-C",W,"show",f"{rev}:{f}"],capture_output=True,text=True).stdout
    imp[mod(f)]=set(re.findall(r'^import\s+(\S+)',src,flags=re.M))
for r in roots:
    down={r}; ch=True
    while ch:
        ch=False
        for m,ims in imp.items():
            if m not in down and ims & down: down.add(m); ch=True
    down.discard('TCSlib')
    print(r.split('.')[-1], len(down), sorted(x.replace('TCSlib.Complexity.','') for x in down))
