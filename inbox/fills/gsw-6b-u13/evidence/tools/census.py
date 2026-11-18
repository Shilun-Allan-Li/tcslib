import re,sys,subprocess
"""Sorry census of a check log: one row per module with the declarations that use `sorry`.
Usage: census.py <log> [<git revision whose sources the log was checked against>]
The declaration name is read at the warning's line of the source (of the given revision, else of
the worktree)."""
L=sys.argv[1]; rev=sys.argv[2] if len(sys.argv)>2 else None; root='/workspace/u13/'
def src(f):
    if rev: return subprocess.run(['git','-C',root,'show',f'{rev}:{f}.lean'],capture_output=True,text=True,check=True).stdout
    return open(root+f+'.lean').read()
txt=open(L).read()
res={}
for m in re.finditer(r"^(TCSlib/[^:]+)\.lean:(\d+):(\d+): warning: declaration uses 'sorry'",txt,re.M):
    f,ln=m.group(1),int(m.group(2))
    line=src(f).split('\n')[ln-1]
    mm=re.search(r'(?:theorem|lemma|def|instance|abbrev)\s+(\S+)',line)
    res.setdefault(f,[]).append(mm.group(1) if mm else f'line{ln}')
tot=0
for f,v in res.items():
    print(f"{f}: {len(v)}: {', '.join(v)}"); tot+=len(v)
print("TOTAL",tot)
