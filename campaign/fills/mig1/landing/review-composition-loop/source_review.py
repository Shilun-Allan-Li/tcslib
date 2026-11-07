"""Audit the exact owned-source delta; this does not parse or elaborate proof terms."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import os
import re

out=Path(__file__).resolve().parent
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad'
relbase='TCSlib/Complexity/TuringMachine/'
paths={'Composition':relbase+'Composition.lean','Wrappers':relbase+'Build/Wrappers.lean','Loop':relbase+'Build/Loop.lean'}
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def mask(s):
    a=list(s); i=0; depth=0; quoted=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): a[i:i+2]='  ';depth+=1;i+=2;continue
            if s.startswith('-/',i): a[i:i+2]='  ';depth-=1;i+=2;continue
            if a[i]!='\n': a[i]=' '
            i+=1;continue
        if quoted:
            if s[i]=='\\':
                a[i]=' ';i+=1
                if i<len(s) and a[i]!='\n': a[i]=' '
            elif s[i]=='"': a[i]=' ';quoted=False
            elif a[i]!='\n': a[i]=' '
            i+=1;continue
        if s.startswith('/-',i): a[i:i+2]='  ';depth=1;i+=2;continue
        if s.startswith('--',i):
            j=s.find('\n',i);j=len(s) if j<0 else j
            a[i:j]=' '*(j-i);i=j;continue
        if s[i]=='"': a[i]=' ';quoted=True
        i+=1
    assert not depth and not quoted
    return ''.join(a)
start=re.compile(r'(?m)^(?P<private>private\s+)?(?P<kind>def|abbrev|lemma|theorem|structure|inductive)\s+(?P<name>[^\s(:{]+)')
command=re.compile(r'(?m)^(?:(?:private\s+)?(?:def|abbrev|lemma|theorem|structure|inductive)\s+|namespace\s+|end(?:\s|$)|attribute\s|set_option\s|variable\s|section(?:\s|$)|open\s)')
def header(block):
    code=mask(block);depth=0;i=0
    while i<len(code):
        c=code[i]
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        if depth==0 and code.startswith(':=',i):
            line=code[code.rfind('\n',0,i)+1:i]
            # Result-type let declarations are not the theorem's value assignment.
            if re.search(r'\blet\b',line): i+=2;continue
            rest=code[i+2:];immediate=rest.lstrip(' \t')
            if immediate.startswith('by') and re.match(r'by\s*\n',immediate):
                following=immediate[immediate.index('\n')+1:]
                first=next((x for x in following.splitlines() if x.strip()),'')
                if len(first)-len(first.lstrip())>2: i+=2;continue
            return block[:i].rstrip()
        i+=1
    # Structures have a where body; unchanged executable blocks are separately byte-compared.
    where=re.search(r'\bwhere\b',code)
    return block[:where.start()].rstrip() if where else block.rstrip()
def declarations(s):
    code=mask(s);ends=[m.start() for m in command.finditer(code)]+[len(s)];result={};order=[]
    for m in start.finditer(code):
        a=m.start();b=next(x for x in ends if x>a)
        doc=re.search(r'(?m)^/[-!]',s[m.end():b])
        if doc: b=m.end()+doc.start()
        block=s[a:b].rstrip()+'\n'
        n=m.group('name');assert n not in result,n
        result[n]=dict(kind=m.group('kind'),private=bool(m.group('private')),block=block,
            header=header(block),line=s.count('\n',0,a)+1,offset=a)
        order.append(n)
    return result,order
# A record assignment nested in an indexed parameter never terminates a header.
test='theorem nested (h : P (input := x)) : True := by\n  trivial\n'
assert header(test)=='theorem nested (h : P (input := x)) : True'
test='private lemma view :\n    let V : T := by\n      exact t\n    P V := by\n  exact h\n'
assert header(test).endswith('P V')
results={};private_changes=[]
for home,rel in paths.items():
    before=(out/('initial-'+home+'.lean.txt')).read_text();after=(wt/rel).read_text()
    old,old_order=declarations(before);new,new_order=declarations(after)
    public_old=[n for n in old_order if not old[n]['private']]
    public_new=[n for n in new_order if not new[n]['private']]
    assert public_old==public_new,(home,'public order/name/visibility')
    assert all(old[n]['header']==new[n]['header'] for n in public_old),(home,'public header')
    executable=[n for n in old if old[n]['kind'] in ('def','abbrev','structure','inductive')]
    assert all(old[n]['block']==new[n]['block'] for n in executable),(home,'executable source')
    assert [l for l in before.splitlines() if l.startswith('import ')]==[l for l in after.splitlines() if l.startswith('import ')]
    attr=lambda s:[l for l in s.splitlines() if l.startswith('attribute ') or l.startswith('@[')]
    assert attr(before)==attr(after),(home,'attributes')
    changes=[n for n in old if old[n]['header']!=new[n]['header']]
    for n in changes:
        assert old[n]['private'] and new[n]['private']
        private_changes.append((home,n,old[n]['header'],new[n]['header']))
    additions=[n for n in new_order if n not in old]
    assert all(new[n]['private'] and new[n]['kind'] in ('lemma','theorem') for n in additions)
    assert not set(old)-set(new)
    results[home]=dict(path=str(wt/rel),sha256=sha(after),initial_sha256=sha(before),
        public_declarations=len(public_old),public_headers_and_order_unchanged=True,
        executable_declarations=len(executable),executable_bytes_unchanged=True,
        imports_and_attributes_unchanged=True,private_header_reexpressions=changes,
        added_private_proof_helpers=additions,
        changed_existing_blocks=[n for n in old_order if old[n]['block']!=new[n]['block']])
assert [(h,n) for h,n,_,_ in private_changes]==[('Wrappers','timedReady_dispatch'),('Wrappers','timed_ledger')]
legacy={'Composition':['condTM_start'],'Wrappers':['timed_capture','timed_control_init','timed_branch_run','timed_read','timed_start'],
        'Loop':['emCall_first_entry']}
for home,names in legacy.items():
    old,_=declarations((out/('initial-'+home+'.lean.txt')).read_text());new,_=declarations((wt/paths[home]).read_text())
    for n in names:
        assert old[n]['block']==new[n]['block'],(home,n,'legacy body changed')
    results[home]['unchanged_legacy_blocks']={n:sha(old[n]['block']) for n in names}
# Warning provenance is exact source-declaration provenance, not a claim to zero global warnings.
loop=(wt/paths['Loop']).read_text();decls,order=declarations(loop)
selected=set(json.loads((out/'Loop-new-seal-v10.coverage.json').read_text())['regions'][i]['name'] for i in range(20))
warnings=[]
for m in re.finditer(r'(?m)^TCSlib/Complexity/TuringMachine/Build/Loop\.lean:(\d+):(\d+): warning:',(out/'loop-final-module-1.out').read_text()):
    line=int(m.group(1));name=max((n for n in order if decls[n]['line']<=line),key=lambda n:decls[n]['line'])
    assert name not in selected,('warning in changed proof',name,line)
    old,_=declarations((out/'initial-Loop.lean.txt').read_text())
    assert old[name]['block']==decls[name]['block'],('warning body changed',name)
    warnings.append(dict(line=line,declaration=name))
results['Loop']['warnings_in_unchanged_legacy_bodies']=warnings
(out/'source-review.json').write_text(json.dumps(results,indent=2)+'\n')
text='# Private header transport re-expressions\n\nBoth private results retain their mathematical content. The explicit let-view transports the branch machine by the approved `branchTM_k` and `branchTM_State` equations before using it in the fixed sum carrier. The old headers required implicit reduction of `branchTM` to type-check. Public headers and every executable definition are byte-preserved.\n'
for home,name,old,new in private_changes:
    text+='\n## '+home+'.'+name+'\n\nOld complete header:\n\n```lean\n'+old+'\n```\n\nNew complete header:\n\n```lean\n'+new+'\n```\n'
text+='\nThe actual fixed-false host table obligations were checked separately in `FixedFalse-v3` and `TimedFixedFalse-v1`; the full repaired conditional consumers and ledger also pass their strict source-region seals. No table-agreement hypothesis was added to a public theorem. Unchanged legacy helpers above remain opaque same-home dependencies; their bodies are not globally sealed.\n'
(out/'private-header-transports.md').write_text(text)
print(json.dumps({h:{k:v for k,v in row.items() if k not in ('warnings_in_unchanged_legacy_bodies',)} for h,row in results.items()},indent=2))
print('Warnings at unchanged legacy bodies:',len(warnings),dict(Counter(r['declaration'] for r in warnings)))
