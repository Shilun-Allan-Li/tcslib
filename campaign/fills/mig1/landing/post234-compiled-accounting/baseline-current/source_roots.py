"""Read-only named-source declaration enumeration. No Lean execution or edits.
Conservative roots compare complete declaration text after comment removal; source/body/type
freeze is separate root-owned evidence. Duplicate and anonymous names are kept explicit.
"""
from pathlib import Path
import re,hashlib,json,subprocess

def strip_comments(text):
 out=[];depth=0;string=False;i=0
 while i<len(text):
  c=text[i]
  if depth:
   if text.startswith('/-',i):out.extend('  ');depth+=1;i+=2
   elif text.startswith('-/',i):out.extend('  ');depth-=1;i+=2
   else:out.append('\n'if c=='\n'else' ');i+=1
  elif string:
   out.append(c);i+=1
   if c=='\\'and i<len(text):out.append(text[i]);i+=1
   elif c=='"':string=False
  elif text.startswith('--',i):
   j=text.find('\n',i);j=len(text)if j<0 else j;out.extend(' '*(j-i));i=j
  elif text.startswith('/-',i):out.extend('  ');depth=1;i+=2
  else:
   out.append(c);i+=1
   if c=='"':string=True
 assert depth==0,'unterminated comment'
 return ''.join(out)

def declarations(text,path):
 clean=strip_comments(text);lines=clean.splitlines(keepends=True);starts=[];stack=[];offset=0
 decl=re.compile(r'^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+(?P<name>[^\s(:{\[]+)')
 scope=re.compile(r'^(?:namespace\s+(\S+)|(?:noncomputable\s+)?section\b\s*(\S*)|(mutual)\b|end\b\s*(\S*))')
 for line_no,line in enumerate(lines,1):
  m=decl.match(line)
  if m:
   name=m['name'];ns='.'.join(n for k,n in stack if k=='namespace')
   if name.startswith('_root_.'):name=name[7:]
   elif ns:name=ns+'.'+name
   starts.append({'name':name,'private':'private'in m['mods'].split(),'kind':m['kind'],'path':path,'line':line_no,'start':offset})
  else:
   q=scope.match(line)
   if q:
    if q[1]:stack.extend(('namespace',n)for n in q[1].split('.'))
    elif q[2]is not None:stack.append(('section',q[2]))
    elif q[3]:stack.append(('mutual',''))
    else:
     for n in reversed(q[4].split('.')):
      if stack and(stack[-1][1]==n or n==''):stack.pop()
  offset+=len(line)
 out=[];seen={}
 for i,r in enumerate(starts):
  end=starts[i+1]['start']if i+1<len(starts)else len(text)
  # Stop before top-level scope/attribute/variable commands, preserving complete proof chunks.
  tail=clean[r['start']:end];stop=re.search(r'(?m)^(?:end\b|namespace\b|section\b|open\b|variable\b|set_option\b|attribute\b|universe\b|#)',tail)
  if stop:end=r['start']+stop.start()
  original=text[r['start']:end].rstrip();tokens=re.sub(r'\s+','',clean[r['start']:end]);key=(r['name'],r['private']);seen[key]=seen.get(key,0)+1
  out.append(r|{'end_line':text.count('\n',0,end)+1,'occurrence':seen[key],'chunk_sha256':hashlib.sha256(original.encode()).hexdigest(),'commentless_tokens_sha256':hashlib.sha256(tokens.encode()).hexdigest(),'chunk':original})
 return out

if __name__=='__main__':
 P=Path('/private/tmp/mig-post234-compiled-accounting');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');old=json.loads((R/'campaign/fills/mig1/landing/compiled-comparison-final/source-proof-roots.json').read_text());revision='b1f553b315f31b949076e91119473ce4070e7d53';rows=[]
 for path in sorted({r['path']for r in old}):
  text=subprocess.check_output(['git','show',revision+':'+path],cwd=R).decode();rows.extend(declarations(text,path))
 checks=[]
 for r in old:
  found=[q for q in rows if q['path']==r['path']and q['name']==r['name']and q['private']==r['private']];assert len(found)==1,(r['path'],r['name'],found)
  checks.append({'name':r['name'],'path':r['path'],'kind':found[0]['kind'],'private':r['private'],'exact_unique_named_source_match':True})
 assert len(checks)==144
 (P/'source-enumerator-historical-check.json').write_text(json.dumps({'revision':revision,'historical144_names_all_uniquely_resolved':True,'method':'independent comment/string-aware source enumerator; whole-chunk differences conservatively select proof roots; no theorem header freeze inferred','matches':checks},indent=2)+'\n')
 print('144 historical roots uniquely resolve in the exact historical source')
