"""Literal header freeze with a balanced proof delimiter, including named arguments."""
from pathlib import Path
import hashlib
import json
import re
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
h=(ROOT/'devtools/seyoon/declfreeze.py').read_text();ns={}
exec(compile(h.split('a = chunks(')[0],'declfreeze-chunk-helper','exec'),ns)


def code(t):
    return t.split('-/',1)[1].lstrip() if t.startswith('/--') else t


def assignment(s):
    stack=[];comment=0;string=False;i=0
    pairs={')':'(',']':'[','}':'{','⟩':'⟨'}
    while i<len(s):
        if comment:
            if s.startswith('/-',i):comment+=1;i+=2;continue
            if s.startswith('-/',i):comment-=1;i+=2;continue
            i+=1;continue
        if string:
            if s[i]=='\\':i+=2;continue
            if s[i]=='"':string=False
            i+=1;continue
        if s.startswith('/-',i):comment=1;i+=2;continue
        if s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j+1;continue
        c=s[i]
        if c=='"':string=True;i+=1;continue
        if c in '([{⟨':stack.append(c)
        elif c in pairs:
            assert stack and stack.pop()==pairs[c],(i,c)
        elif not stack and s.startswith(':=',i):return i
        i+=1
    return None


def split(t):
    s=code(t);i=assignment(s)
    return (s,None) if i is None else (s[:i],s[i+2:])


source=(OUT/'Catalog-current.lean.txt').read_text();base=(OUT/'Catalog-base1160.lean.txt').read_text()
a=ns['chunks'](base);b=ns['chunks'](source);A={n:(p,t) for n,p,t in a};B={n:(p,t) for n,p,t in b}
shared=A.keys()&B.keys();rows=[]
for n in [n for n,_,_ in b if n in shared]:
    ha,ba=split(A[n][1]);hb,bb=split(B[n][1]);assert ha==hb,n
    isproof=bool(re.match(r'(?:(?:private|protected)\s+)*(?:theorem|lemma)\b',hb))
    if not isproof:assert A[n][1]==B[n][1],n
    rows.append(dict(name=n,private=B[n][0],header_literal_equal=True,
                     header_sha256=hashlib.sha256(hb.encode()).hexdigest(),
                     body_literal_equal=ba==bb,proof=isproof,
                     body_delimiter='balanced depth-zero :=; nested named arguments ignored'))
assert [n for n,_,_ in a if n in shared]==[n for n,_,_ in b if n in shared]
changed=[r['name'] for r in rows if not r['body_literal_equal']]
added=[n for n in B if n not in A];assert len(changed)==24 and len(added)==3
assert all(B[n][0] for n in added)
imports_a=re.findall(r'^import .*',base,re.M);imports_b=re.findall(r'^import .*',source,re.M)
assert imports_b==imports_a[:3]+['import TCSlib.Complexity.TuringMachine.Build.Primitives']+imports_a[3:]
r=dict(all_shared_headers_literal_equal=True,all_shared_definition_tables_and_types_literal_equal=True,
       all_retained_relative_order_equal=True,shared_count=len(shared),retained=rows,
       changed_existing_proof_bodies=changed,new_private_proof_helpers=added,
       actual_proof_changes_including_additions=len(changed)+len(added),
       approved_import_addition_only='TCSlib.Complexity.TuringMachine.Build.Primitives',
       delimiter_method='Balanced lexical depth-zero :=; handles comments, strings, (), [], {}, and angle constructors. Unlike first-:= keys, named arguments in headers do not truncate statements.',
       source_sha256=hashlib.sha256(source.encode()).hexdigest(),base_sha256=hashlib.sha256(base.encode()).hexdigest())
(OUT/'freeze.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['all_shared_headers_literal_equal','all_shared_definition_tables_and_types_literal_equal','all_retained_relative_order_equal','shared_count','actual_proof_changes_including_additions','approved_import_addition_only']},indent=2))
