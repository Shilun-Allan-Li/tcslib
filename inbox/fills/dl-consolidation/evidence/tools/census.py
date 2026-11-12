import re,sys
L=sys.argv[1]; root='/workspace/dlc/'
txt=open(L).read()
res={}
for m in re.finditer(r"^(TCSlib/[^:]+)\.lean:(\d+):(\d+): warning: declaration uses 'sorry'",txt,re.M):
    f,ln=m.group(1),int(m.group(2))
    line=open(root+f+'.lean').read().split('\n')[ln-1]
    mm=re.search(r'(?:theorem|lemma|def|instance|abbrev)\s+(\S+)',line)
    res.setdefault(f,[]).append(mm.group(1) if mm else f'line{ln}')
tot=0
for f,v in res.items():
    print(f"{f}: {len(v)}: {', '.join(v)}"); tot+=len(v)
print("TOTAL",tot)
