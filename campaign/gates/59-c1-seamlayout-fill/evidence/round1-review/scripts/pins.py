import re, sys, subprocess
W, script, rev = sys.argv[1:4]
src=open(script).read()
pins=re.findall(r'(TCSlib/[A-Za-z0-9_/]+\.lean)[:\s=]+["\']?([0-9a-f]{8,40})', src)
seen=set(); ok=0; bad=[]
for p,h in pins:
    if (p,h) in seen: continue
    seen.add((p,h))
    actual=subprocess.run(["git","-C",W,"rev-parse",f"{rev}:{p}"],capture_output=True,text=True).stdout.strip()
    if actual.startswith(h): ok+=1
    else: bad.append((p,h,actual))
print(f"{script.split('/')[-1]} vs {rev}: {len(seen)} pins, {ok} match, {len(bad)} differ")
for b in bad: print("  DIFFER", b)
