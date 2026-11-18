"""Read-only import graph; strips nested Lean comments and string literals. No Lean."""
from pathlib import Path
import re,sys
root=Path(sys.argv[1]);todo=sys.argv[2:];seen=set()
def imports(p):
 s=p.read_text();a=[];i=0;depth=0;quote=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    if s[i]=='\n':a.append('\n')
    i+=1
  elif quote:
   if s[i]=='\\':i+=2
   elif s[i]=='"':quote=False;i+=1
   else:
    if s[i]=='\n':a.append('\n')
    i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':quote=True;i+=1
  else:a.append(s[i]);i+=1
 return [x for l in ''.join(a).splitlines()if re.match(r'^\s*(public |meta )?import ',l)for x in re.sub(r'^\s*(public |meta )?import ','',l).split()if x.startswith(('Mathlib.','TCSlib.'))]
def path(m):
 for base in [root,root/'.lake/packages/mathlib']:
  p=base/(m.replace('.','/')+'.lean')
  if p.exists():return p
while todo:
 m=todo.pop()
 if m in seen:continue
 seen.add(m);p=path(m)
 if p:todo.extend(imports(p))
print('\n'.join(sorted(seen)))
