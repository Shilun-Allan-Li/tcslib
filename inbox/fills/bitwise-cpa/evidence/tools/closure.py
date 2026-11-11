import re, sys
order = [l.strip() for l in open(sys.argv[1]) if l.strip()]
target = sys.argv[2]
S = set(order)
def imps(m):
    out=[]
    for l in open(m+'.lean'):
        mm = re.match(r'^import\s+(TCSlib\S*)', l)
        if mm: out.append(mm.group(1).replace('.','/'))
    return out
need=set(); st=[target]
while st:
    m=st.pop()
    for i in imps(m):
        if i not in need:
            need.add(i); st.append(i)
for m in order:
    if m in need: print(m)
missing = need - S
if missing: print("MISSING", missing, file=sys.stderr)
