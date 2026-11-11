import re, sys, os
def imps(m):
    out=[]
    for l in open(m+'.lean'):
        mm = re.match(r'^import\s+(TCSlib\S*)', l)
        if mm: out.append(mm.group(1).replace('.','/'))
    return out
roots = sys.argv[1:]
need=set(roots); st=list(roots)
while st:
    m=st.pop()
    for i in imps(m):
        if i not in need: need.add(i); st.append(i)
# topo order
order=[]; seen=set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for i in imps(m): visit(i)
    order.append(m)
for r in roots: visit(r)
print("\n".join(order))
