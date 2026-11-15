"""Read rule heads from balanced explicit simp/rw/dsimp/unfold arguments."""
import re
IDENTIFIER=re.compile(r"[^\W\d][\w.']*",re.UNICODE)
def split_items(text):
 depth=0;start=0
 for i,c in enumerate(text):
  if c in '([{⟨':depth+=1
  elif c in ')]}⟩':depth-=1
  elif c==','and depth==0:yield text[start:i];start=i+1
 yield text[start:]
def head(item):
 item=item.strip().lstrip('←-↓↑').lstrip()
 while item.startswith('('):item=item[1:].lstrip()
 m=IDENTIFIER.match(item)
 if not m or m[0]in {'show','by','fun','if','match'}:return None
 return m[0]
def arguments(code):
 for m in re.finditer(r'\b(?:simp(?:_rw)?|simpa|dsimp|rw|erw|unfold)\b',code):
  tail=code[m.end():]
  b=re.match(r'(?:\s+only)?\s*\[',tail)
  if b:
   start=m.end()+b.end();depth=1;j=start
   while j<len(code)and depth:
    if code[j]=='[':depth+=1
    elif code[j]==']':depth-=1
    j+=1
   if depth:raise ValueError('unclosed tactic bracket')
   items=split_items(code[start:j-1])
  elif m.group()=='unfold':items=tail.split('\n',1)[0].split(' at ',1)[0].split()
  else:continue
  for item in items:
   token=head(item)
   if token:yield m.start(),m.group(),token
