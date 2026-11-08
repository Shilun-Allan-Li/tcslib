from pathlib import Path
import re,json,hashlib,collections
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
code=(O/'prepare-candidate.py').read_text();ns={};exec(code[code.index('def mask('):code.index('\nsources=')],ns);mask=ns['mask']
command=re.compile(r'^(?:(?P<scope>namespace|section|end)\b(?P<label>[^\n]*))|^(?P<decl>(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+(?P<name>[^\s:(\[{]+))',re.M)
def extract(s):
    ms=mask(s);matches=list(command.finditer(ms));scope=[];out=[]
    for i,m in enumerate(matches):
        if m['scope']:
            k=m['scope'];label=m['label'].strip().split()[0] if m['label'].strip() else ''
            if k in ('namespace','section'):scope.append((k,label))
            elif scope:
                if not label:scope.pop()
                else:
                    while scope:
                        k2,l2=scope.pop()
                        if l2==label or l2.split('.')[-1]==label:break
            continue
        a=m.start();name='.'.join([v for k,v in scope if k=='namespace']+[m['name']]);stack=[];j=m.end();sep=None
        pairs={'(':')','[':']','{':'}','⟨':'⟩'}
        while j<len(ms):
            if ms[j] in pairs:stack.append(pairs[ms[j]])
            elif stack and ms[j]==stack[-1]:stack.pop()
            elif not stack and (ms.startswith(':=',j) or re.match(r'where\b',ms[j:])):
                sep=j;break
            j+=1
        if sep is None:raise RuntimeError('no declaration body: '+name)
        nxt=next((z for z in matches[i+1:] if z['decl'] or z['scope']),None);end=nxt.start() if nxt else len(s)
        doc=s.rfind('/--',sep,end)
        if doc>=0 and not mask(s[doc:end]).strip():end=doc
        # Attribute or scoped-open commands preceding the next declaration belong
        # to that next declaration, not to this proof's body.
        tail=re.search(r'\n(?:@\[|open\s+[^\n]+\s+in\s*$)',s[sep:end],re.M)
        if tail:end=sep+tail.start()
        out.append({'name':name,'lexical_name':m['name'],'kind':m['kind'],'private':bool(re.match(r'private\b',m['decl'])),
                    'line':s.count('\n',0,a)+1,'header':s[a:sep].rstrip(),'body':s[sep:end].strip(),'full':s[a:end].strip()})
    return out
changed=[];removed=[];added=[];header_differences=[];definition_differences=[];imports=[];roots=[]
for r in json.loads((O/'current-source-map.json').read_text()):
    p=r['path'];old=(O/'source-before'/(p+'.txt')).read_text();new=(W/p).read_text();a=extract(old);b=extract(new)
    def keyed(xs):
        c=collections.Counter();out={}
        for x in xs:c[x['name']]+=1;out[(x['name'],c[x['name']])]=x
        return out
    ad=keyed(a);bd=keyed(b)
    for k in ad.keys()-bd.keys():removed.append({'path':p,**ad[k]})
    for k in bd.keys()-ad.keys():added.append({'path':p,**bd[k]})
    for k in ad.keys()&bd.keys():
        u,v=ad[k],bd[k]
        if u['header']!=v['header']:header_differences.append({'path':p,'old':u,'new':v})
        if u['body']!=v['body']:
            row={'path':p,'name':v['name'],'lexical_name':v['lexical_name'],'kind':v['kind'],'private':v['private'],'baseline_line':u['line'],'current_line':v['line'],'header':v['header'],'before_body_sha256':hashlib.sha256(u['body'].encode()).hexdigest(),'after_body_sha256':hashlib.sha256(v['body'].encode()).hexdigest()}
            changed.append(row)
            if v['kind'] not in ('lemma','theorem'):definition_differences.append({'path':p,'old':u,'new':v})
            else:roots.append(row)
    oi=re.findall(r'^import\s+[^\n]+',old,re.M);ni=re.findall(r'^import\s+[^\n]+',new,re.M)
    if oi!=ni:imports.append({'path':p,'removed':[x for x in oi if x not in ni],'added':[x for x in ni if x not in oi]})
for r in added:
    if r['kind'] in ('lemma','theorem'):roots.append({k:v for k,v in r.items() if k not in ['body','full']})
receipt={'method':'comment/string-masked lexical command and balanced-header comparison; native checks separately validate the concrete files','unchanged_existing_headers':not header_differences,'unchanged_definition_bodies':not definition_differences,'existing_header_differences':header_differences,'definition_differences':definition_differences,'changed_proof_roots':changed,'removed_declarations':removed,'new_declarations':added,'import_changes_held':imports,'no_simp_attribute_added':all('simp' not in r['header'] for r in added)}
(O/'declaration-freeze.json').write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n')
(O/'changed-native-roots.json').write_text(json.dumps(roots,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'changed_proof_roots':len(changed),'removed':[(r['path'],r['name']) for r in removed],'added':[(r['path'],r['name']) for r in added],'header_differences':len(header_differences),'definition_body_differences':len(definition_differences),'held_imports':len(imports)},ensure_ascii=False))
for x in header_differences+definition_differences:print(x['path'],x['old']['name'])
