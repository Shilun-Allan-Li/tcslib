import re,sys,subprocess
head,diff,names=sys.argv[1],sys.argv[2],sys.argv[3]
# added line numbers in head
added=set(); ln=0
for l in open(diff):
    m=re.match(r'@@ -\d+(?:,\d+)? \+(\d+)',l)
    if m: ln=int(m.group(1)); continue
    if l.startswith('+++') or l.startswith('---'): continue
    if l.startswith('+'): added.add(ln); ln+=1
    elif l.startswith('-'): pass
    else: ln+=1
src=open(head).read()
lines=src.split('\n')
starts=[0]
for l in lines: starts.append(starts[-1]+len(l)+1)
def lineof(pos):
    import bisect; return bisect.bisect_right(starts,pos)
foreign=set()
for n in open(names):
    n=n.strip()
    if not n: continue
    foreign.add(n.split('.')[-1]); foreign.add(n)
    parts=n.split('.')
    for k in range(len(parts)): foreign.add('.'.join(parts[k:]))
lists=0; hits=[]
for m in re.finditer(r'\b(rw|rwa|simp only|simp|simpa only|simpa|simp_rw|dsimp only|dsimp|nth_rw \d+|erw)\s*\[',src):
    if lineof(m.start()) not in added: continue
    i=m.end(); depth=1
    while depth and i<len(src):
        if src[i]=='[': depth+=1
        elif src[i]==']': depth-=1
        i+=1
    body=src[m.end():i-1]; lists+=1
    for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'.?!₀-₉]*",body):
        t=tok.lstrip('←').strip()
        if t in foreign: hits.append((lineof(m.start()),m.group(1),t))
unf=0
for m in re.finditer(r'\b(unfold|delta)\s+([^\n]*)',src):
    if lineof(m.start()) not in added: continue
    unf+=1
    for tok in m.group(2).split():
        if tok in foreign: hits.append((lineof(m.start()),m.group(1),tok))
        else: print('UNFOLD',lineof(m.start()),tok)
print('rewrite/simp lists in added code:',lists,'; unfold/delta:',unf)
for h in hits: print('HIT',*h)
print('hits:',len(hits))
