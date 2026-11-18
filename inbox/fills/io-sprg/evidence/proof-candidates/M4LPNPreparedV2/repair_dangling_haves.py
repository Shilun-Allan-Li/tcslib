"""Text-only repair of missing typed-have assignments, including bullet-prefixed headers."""
import re

def repair(s):
 lines=s.splitlines();changes=[];i=0
 while i<len(lines):
  l=lines[i];m=re.match(r'^\s*(?:[·|]\s*)?have\b',l)
  if not m:i+=1;continue
  col=l.index('have');header=l[l.index('have'):]
  if ':' not in header or ':=' in header:i+=1;continue
  j=i+1
  while j<len(lines):
   n=lines[j]
   if ':=' in header:break
   if n.strip().startswith('·') and len(n)-len(n.lstrip())==col:
    lines[j-1]+=' := ?_';lines.insert(j,' '*col+'swap')
    changes.append({'line':i+1,'header':l.strip()});j+=1;break
   if n.strip() and len(n)-len(n.lstrip())<=col:break
   header+='\n'+n;j+=1
  i=max(i+1,j)
 return '\n'.join(lines)+'\n',changes
