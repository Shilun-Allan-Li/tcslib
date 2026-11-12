# Print, in a stable topological order, the modules of the closure of the given roots that have
# no olean yet in the pk tree.
import re, os, sys
F='/home/user/fill'; OL=F+'/.lake/pk-oleans'
def imps(m):
    return [x.group(1).replace('.','/') for l in open(F+'/'+m+'.lean') for x in [re.match(r'^import\s+(TCSlib\S*)',l)] if x]
seen=[]; vis=set()
def visit(m):
    if m in vis: return
    vis.add(m)
    for i in imps(m): visit(i)
    seen.append(m)
for r in sys.argv[1:]: visit(r)
for m in seen:
    if m in sys.argv[1:]: continue
    if not os.path.exists(OL+'/'+m+'.olean'): print(m)
