import re, sys
src=open(sys.argv[1]).read().split('\n')
DECL=re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance|inductive|structure)\s+(\S+)')
decls=[]; i=0; doc=None; docstart=None
n=len(src)
starts=[]
for i,l in enumerate(src):
    m=DECL.match(l)
    if m: starts.append((i,m.group(4),m.group(5)))
res=[]
for k,(i,kind,name) in enumerate(starts):
    end = starts[k+1][0] if k+1<len(starts) else n
    # docstring immediately above
    j=i-1; d=[]
    if j>=0 and src[j].rstrip().endswith('-/'):
        while j>=0 and not src[j].lstrip().startswith('/--'): d.append(src[j]); j-=1
        if j>=0: d.append(src[j])
    doc='\n'.join(reversed(d))
    # cut body at the next docstring start
    body=src[i:end]
    for t,l in enumerate(body):
        if t>0 and l.startswith('/--'): body=body[:t]; break
    text='\n'.join(body)
    if kind in ('theorem','lemma') and ':= by' in text:
        after=text.split(':= by',1)[1]
        nb=[l for l in after.split('\n') if l.strip()]
        res.append((name,kind,len(nb),bool(doc),'Proof sketch' in doc))
big=[r for r in res if r[2]>20]
print(f"theorems/lemmas with tactic proofs: {len(res)}; over 20 non-blank proof lines: {len(big)}; of them without 'Proof sketch' in the docstring: {sum(1 for r in big if not r[4])}")
for r in sorted(big,key=lambda r:-r[2]): print(f"  {r[0]:28s} {r[1]:8s} {r[2]:4d}  docstring={r[3]}  sketch={r[4]}")
