from pathlib import Path
import re,json,hashlib
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
code=(O/'prepare-candidate.py').read_text()
ns={};exec(code[code.index('def mask('):code.index('\nsources=')],ns);mask=ns['mask']
declpat=re.compile(r'^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:(\[{]+)',re.M)
def term(s,i):
    while i<len(s) and s[i].isspace():i+=1
    a=i;pairs={'(':')','[':']','{':'}','⟨':'⟩'}
    if i<len(s) and s[i] in pairs:
        stack=[pairs[s[i]]];i+=1
        while stack and i<len(s):
            if s[i] in pairs:stack.append(pairs[s[i]])
            elif s[i]==stack[-1]:stack.pop()
            i+=1
        return a,i
    m=re.match(r'[^\s()\[\]{},:=<>≤≥∧∨]+',s[i:])
    return a,i+len(m.group()) if m else i

rows=[];remaining=[];successors=[]
edits=json.loads((O/'candidate-edits.json').read_text())
for cp in sorted((O/'source-before'/'TCSlib').rglob('*.lean.txt')):
    p=str(cp.relative_to(O/'source-before'))[:-4];s=cp.read_text();ms=mask(s);ds=list(declpat.finditer(ms));new=(W/p).read_text()
    def info(a,b):
        before=[d for d in ds if d.start()<=a];d=before[-1] if before else None
        end=ds[ds.index(d)+1].start() if d is not None and ds.index(d)+1<len(ds) else len(s)
        name=d.group(1) if d else '<preamble>'
        lo=max(0,s.rfind('\n',0,max(0,a-150)));hi=s.find('\n',min(len(s),b+400));hi=len(s) if hi<0 else hi
        return {'path':p,'line':s.count('\n',0,a)+1,'declaration_lexical':name,'context':s[lo:hi],
                'same_declaration_edits':[r['id'] for r in edits if r['path']==p and r['declaration_lexical']==name],
                'full_before_source':str(cp),'current_source_changed':new!=s}
    for m in re.finditer(r'(?<!\w)(?:\w+\.)?runFrom\b',ms):
        i=m.end();a,b=term(ms,i)
        while a<b and ':=' in ms[a:b] and ms[a]=='(':i=b;a,b=term(ms,i)
        c,d=term(ms,b)
        if ms[c:d]=='1':
            r=info(m.start(),d);r['application_fragment']=s[m.start():d]
            rows.append(r)
    for m in re.finditer(r'(?<!\w)(?:MultiTapeTM\.)?runFrom_succ_eq_step\x27?\b',ms):
        r=info(m.start(),m.end());r['shape']='successor equation use';successors.append(r)
    # Collect every remaining changed-source successor/zero declaration, not capped.
    nd=list(declpat.finditer(mask(new)))
    for j,d in enumerate(nd):
        end=nd[j+1].start() if j+1<len(nd) else len(new);ch=new[d.start():end]
        if 'runFrom_succ_eq_step' in mask(ch) and 'runFrom_zero' in mask(ch):
            remaining.append({'path':p,'line':new.count('\n',0,d.start())+1,'declaration_lexical':d.group(1),
                              'full_chunk':ch,'current_source_changed':new!=s})
(O/'literal-one-candidate-census.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(O/'all-successor-candidate-census.json').write_text(json.dumps(successors,indent=2,ensure_ascii=False)+'\n')
(O/'remaining-successor-zero-declarations.json').write_text(json.dumps(remaining,indent=2,ensure_ascii=False)+'\n')
uniq={}
for r in rows:
    if not r['same_declaration_edits']:
        uniq[(r['path'],r['declaration_lexical'])]=r
print('literal one occurrences',len(rows),'successor occurrences',len(successors),'remaining successor-zero declarations',len(remaining),'literal declarations without edit',len(uniq))
for r in uniq.values():print(r['path']+':'+str(r['line'])+' '+r['declaration_lexical']+' '+re.sub(r'\s+',' ',r['application_fragment'])[:180])
print('REMAINING SUCCESSOR ZERO')
for r in remaining:print(r['path']+':'+str(r['line'])+' '+r['declaration_lexical'])
