import csv,hashlib,json,re,subprocess,sys
from pathlib import Path
out=Path(__file__).resolve().parent
base='5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
head=sys.argv[1] if len(sys.argv)>1 else subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
paths=subprocess.check_output(['git','diff','--name-only','--diff-filter=A',base,head],text=True).splitlines()
allrows=[];sizes=[];unnamed=[]
for path in paths:
    data=subprocess.check_output(['git','show',head+':'+path]);s=data.decode();lines=s.splitlines()
    docs=list(re.finditer(r'/--([\s\S]*?)-/',s));offset=0;stack=[];decls=[]
    for lineno,line in enumerate(lines,1):
        ns=re.match(r'^(namespace|section)\s+(\S+)',line)
        if ns:stack.append((ns[1],ns[2]))
        if re.match(r'^end(?:\s|$)',line):
            if stack:stack.pop()
        m=re.match(r'^(?P<mod>(?:(?:noncomputable|private|protected)\s+)*)(?P<kind>def|abbrev|theorem|lemma|structure|inductive|instance)\b\s*(?P<name>[^\s({:\[]+)?',line)
        if m and 'private' not in m['mod']:
            name=m['name']
            if not name:
                name=f'[anonymous instance at line {lineno}]'
                unnamed.append((path,lineno))
            nslist=[v for k,v in stack if k=='namespace']
            fullname='.'.join(nslist+[name])
            prior=[d for d in docs if d.end()<=offset]
            doc=prior[-1].group(1).strip() if prior else ''
            if prior and s[prior[-1].end():offset].strip():doc=''
            doc=' '.join(doc.split())
            citations=re.findall(r'\[JLS26,\s*(.*?)\]',doc)
            # Tags are transcribed, not invented; glue inherits the grouped table's mapping.
            cites='; '.join(citations) or 'Glue / reader / interface; see grouped fidelity table'
            dvs=sorted(set(re.findall(r'\bDv\d+\b',doc)),key=lambda v:int(v[2:]))
            reason=doc.split('**Proof sketch.**')[0].strip()
            state='M0 sorry' if ':= sorry' in line else ''
            row=[cites,fullname,f'{path}:{lineno}',','.join(dvs) or 'Owner/group deviations',m['kind'],reason]
            allrows.append(row);decls.append(row)
        offset+=len(line)+1
    sizes.append({'path':path,'lines':len(lines),'max_width':max(map(len,lines),default=0),
                  'bytes':len(data),'lexical_public_declarations':len(decls),
                  'sorry_tokens':len(re.findall(r'\bsorry\b',s)),
                  'sha256':hashlib.sha256(data).hexdigest()})
with (out/'fidelity-declarations.tsv').open('w') as f:
    w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['paper_item_page_tag','Lean_name','file_line','deviations_in_own_docstring','kind','statement_prose']);w.writerows(allrows)
with (out/'sizes.tsv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(sizes[0]),delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(sizes)
(out/'source-snapshot.json').write_text(json.dumps({'base':base,'candidate':head,'new_files':sizes,'lexical_public_declaration_rows':len(allrows),'anonymous_instances':unnamed,'counts':{'new_files':len(sizes),'lines':sum(x['lines'] for x in sizes),'bytes':sum(x['bytes'] for x in sizes),'sorry_tokens':sum(x['sorry_tokens'] for x in sizes),'max_width':max(x['max_width'] for x in sizes)}},indent=2)+'\n')
print(json.dumps({'rows':len(allrows),'counts':{'new_files':len(sizes),'lines':sum(x['lines'] for x in sizes),'bytes':sum(x['bytes'] for x in sizes),'sorry_tokens':sum(x['sorry_tokens'] for x in sizes),'max_width':max(x['max_width'] for x in sizes)},'anonymous_instances':unnamed}))
