import json, re, hashlib, difflib
from pathlib import Path

W = Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
O = Path('/private/tmp/ab34-ro1-integration')
HOME = 'TCSlib.Complexity.TuringMachine.CfgFacts'
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def mask(s):
    out=list(s); i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): out[i:i+2]='  ';depth+=1;i+=2
            elif s.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif string:
            if s[i]=='\\':
                out[i]=' ';i+=1
                if i<len(s) and s[i]!='\n':out[i]=' '
                i+=1
            elif s[i]=='"':out[i]=' ';string=False;i+=1
            else:
                if s[i]!='\n':out[i]=' '
                i+=1
        elif s.startswith('--',i):
            j=s.find('\n',i)
            if j<0:j=len(s)
            out[i:j]=' '*(j-i);i=j
        elif s.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2
        elif s[i]=='"':out[i]=' ';string=True;i+=1
        else:i+=1
    return ''.join(out)

sources={str(p.relative_to(W)):p.read_text() for p in sorted((W/'TCSlib').rglob('*.lean'))}
sources['TCSlib/Complexity/TuringMachine/CfgFacts.lean']=(O/'CfgFacts.before.lean.txt').read_text()
proposed=dict(sources)
proposed['TCSlib/Complexity/TuringMachine/CfgFacts.lean']=(O/'CfgFacts.proposed.lean.txt').read_text()
modules={p[:-5].replace('/','.'):p for p in sources}
graph={m: re.findall(r'^import\s+(\S+)',mask(sources[p]),re.M) for m,p in modules.items()}
def closure(m,g):
    seen=set(); todo=[m]
    while todo:
        n=todo.pop()
        if n not in seen:seen.add(n);todo.extend(g.get(n,[]))
    return seen
ancestors=closure(HOME,graph)
declpat=re.compile(r'^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:(\[{]+)',re.M)
decls={p:list(declpat.finditer(mask(s))) for p,s in sources.items()}
def decl_at(p,pos):
    hits=[m for m in decls[p] if m.start()<=pos]
    return hits[-1].group(1) if hits else '<preamble>'
rows=[]; edits={p:[] for p in sources}
def add(p,a,b,new,kind,disposition='candidate exact mechanical repoint',reason=''):
    row={'id':f'RO1-{len(rows)+1:04d}','path':p,'line':sources[p].count('\n',0,a)+1,
         'declaration_lexical':decl_at(p,a),'kind':kind,'before':sources[p][a:b],'after':new,
         'disposition':disposition,'reason':reason,'baseline_sha256':sha(sources[p])}
    rows.append(row)
    if new is not None:edits[p].append((a,b,new,row['id']))
    return row

# Delete the approved former Bool API and four private one-step copies, including
# their own documentation. The XR scoped `open ... in` belongs to that theorem.
removed={'TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean':'runFrom_one',
 'TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean':'qy_run_one',
 'TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean':'xr_runFrom_one',
 'TCSlib/Complexity/ClassNP/SAT.lean':'satRed_one',
 'TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean':'recordStep_runFrom_one'}
removed_ranges={}
for p,name in removed.items():
    ds=decls[p]; i=next(i for i,m in enumerate(ds) if m.group(1)==name)
    start=ds[i].start();s=sources[p]
    docstart=s.rfind('/--',0,start)
    assert docstart>=0 and not mask(s[docstart:start]).strip()
    start=docstart
    if name=='xr_runFrom_one':
        prefix='open MultiTapeTM in\n';assert s[start-len(prefix):start]==prefix;start-=len(prefix)
    # Stop before the next declaration's own docstring, preserving it.
    end=ds[i+1].start()
    nextdoc=s.rfind('/--',ds[i].end(),end)
    if nextdoc>=0:end=nextdoc
    while end>start and s[end-1]=='\n':end-=1
    end+=2
    assert s[end-2:end]=='\n\n'
    removed_ranges[p]=(start,end)
    add(p,start,end,'','remove former one-step copy',reason='generic API explicitly approved; every client is repointed')

pair=re.compile(r'(?<![\w.])(?:MultiTapeTM\.)?runFrom_succ_eq_step\x27?(?:\s*\((?:tm|cfg|t)\s*:=\s*[^()\n]*\))*\s*,\s*(?:MultiTapeTM\.)?runFrom_zero\b')
old=re.compile(r'(?<![\w.])(?:Turing\.)?runFrom_one\b|\b(?:qy_run_one|xr_runFrom_one|satRed_one|recordStep_runFrom_one)\b')
for p,s in sources.items():
    ms=mask(s);mod=p[:-5].replace('/','.')
    def taken(a):return p in removed_ranges and removed_ranges[p][0]<=a<removed_ranges[p][1]
    for m in pair.finditer(ms):
        if taken(m.start()):continue
        if mod in ancestors:
            add(p,m.start(),m.end(),None,'successor/zero pair','blocked home dependency cycle','owner lies in CfgFacts dependency closure; importing home would create a cycle')
        else:add(p,m.start(),m.end(),'MultiTapeTM.runFrom_one','successor/zero pair')
    for m in old.finditer(ms):
        if not taken(m.start()):add(p,m.start(),m.end(),'MultiTapeTM.runFrom_one','former one-step name client')
    trans=re.compile(r'MultiTapeTM\.runFrom_succ_eq_step\.trans\s+MultiTapeTM\.runFrom_zero')
    for m in trans.finditer(ms):add(p,m.start(),m.end(),'MultiTapeTM.runFrom_one _ _','successor/zero transitivity term')
    # Preserve the literal `show` statement and change only its rfl proof.
    for m in re.finditer(r'\bshow\s+(?:(?!\bfrom\b).){0,1100}?\bfrom\s+rfl\b',ms,re.S):
        z=m.group()
        if '.runFrom' in z and re.search(r'\s1\s*=',z) and '.step' in z:
            a=m.end()-3
            add(p,a,m.end(),'MultiTapeTM.runFrom_one _ _','show one-step equality / rfl proof')

def exact(p,before,after,kind,expected=1):
    s=sources[p];count=s.count(before);assert count==expected,(p,before,count,expected)
    for m in re.finditer(re.escape(before),s):add(p,m.start(),m.end(),after,kind)

exact('TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean',
 'simp [MultiTapeTM.runFrom]','exact MultiTapeTM.runFrom_one _ _','literal one-step local proof',2)
exact('TCSlib/Complexity/TuringMachine/CounterProg.lean',
 '    fun c => rfl\n  rw [henc]', '    MultiTapeTM.runFrom_one _\n  rw [henc]','literal one-step local function proof')
exact('TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean',
 'simp [runFrom, hstep]','rw [MultiTapeTM.runFrom_one, hstep]','literal one-step local proof')
for p,n in [('TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean',3),
 ('TCSlib/Complexity/TuringMachine/Build/StepClock.lean',1)]:
    exact(p,'MultiTapeTM.runFrom, Function.iterate_one','MultiTapeTM.runFrom_one','explicit iterate-one simplification',n)
for p,n in [('TCSlib/Complexity/ClassNP/EXP.lean',1),
 ('TCSlib/Complexity/ClassNP/Nondeterminism.lean',2),
 ('TCSlib/Complexity/CookLevin/Hardness.lean',1)]:
    exact(p,'MultiTapeTM.runFrom, MultiTapeTM.step','MultiTapeTM.runFrom_one, MultiTapeTM.step','literal one-step simp argument',n)
exact('TCSlib/Complexity/SpaceComplexity/Inclusions.lean',
 'simpa [MultiTapeTM.runFrom, moveInputPos_zero, sub_eq_add_neg]',
 'simpa [MultiTapeTM.runFrom_one, moveInputPos_zero, sub_eq_add_neg]','one-step simpa argument')

for p,es in edits.items():
    if not es:continue
    es.sort()
    assert all(es[i][1]<=es[i+1][0] for i in range(len(es)-1)),p
    s=sources[p]
    for a,b,new,_ in reversed(es):s=s[:a]+new+s[b:]
    proposed[p]=s

# Insert the precise home import only if the evolving proposed dependency closure
# does not already provide it. This avoids unnecessary downstream direct imports.
changed={p for p in sources if proposed[p]!=sources[p]}
ordered=[];seen=set();active=set()
def visit(m):
    if m in active:raise RuntimeError('baseline import cycle '+m)
    if m in seen:return
    active.add(m)
    for n in graph.get(m,[]):
        if n in modules:visit(n)
    active.remove(m);seen.add(m)
    if modules.get(m) in changed:ordered.append(modules[m])
for m in sorted(modules):visit(m)
g={m:list(ns) for m,ns in graph.items()};imports=[]
for p in ordered:
    m=p[:-5].replace('/','.')
    if m==HOME:continue
    needs='MultiTapeTM.runFrom_one' in mask(proposed[p])
    if needs and HOME not in closure(m,g):
        assert m not in closure(HOME,g),m
        line='import '+HOME+'\n'
        matches=list(re.finditer(r'^import[^\n]*\n',proposed[p],re.M));assert matches,p
        pos=matches[-1].end();proposed[p]=proposed[p][:pos]+line+proposed[p][pos:]
        g[m].append(HOME)
        imports.append({'path':p,'addition':line.strip(),'status':'HELD HYPOTHETICAL / not authorized to publish',
                        'reason':'exact generic one-step API unavailable through current proposed imports',
                        'baseline_imports':graph[m],'proposed_imports':g[m],
                        'baseline_closure':sorted(closure(m,graph)),
                        'proposed_closure':sorted(closure(m,g)),
                        'cycle':False})

for p in sources:
    bp=O/'source-before'/(p+'.txt');bp.parent.mkdir(parents=True,exist_ok=True);bp.write_text(sources[p])
    if p in changed:
        pp=O/'source-candidate'/(p+'.txt');pp.parent.mkdir(parents=True,exist_ok=True);pp.write_text(proposed[p])
(O/'candidate-edits.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(O/'held-imports.json').write_text(json.dumps(imports,indent=2,ensure_ascii=False)+'\n')
(O/'proposed-import-graph.json').write_text(json.dumps(g,indent=2)+'\n')
(O/'changed-owners-topological.json').write_text(json.dumps(ordered,indent=2)+'\n')
(O/'candidate-source-map.json').write_text(json.dumps([{'path':p,'baseline_sha256':sha(sources[p]),'candidate_sha256':sha(proposed[p])} for p in ordered],indent=2)+'\n')
patch=''.join(''.join(difflib.unified_diff(sources[p].splitlines(True),proposed[p].splitlines(True),fromfile='a/'+p,tofile='b/'+p)) for p in sorted(changed))
(O/'initial-candidate.patch').write_text(patch)
print(json.dumps({'source_files':len(sources),'candidate_rows':len(rows),'mechanical_edit_rows':sum(r['after'] is not None for r in rows),'held_import_additions':len(imports),'changed_owners':len(ordered),'cycle_blocked_rows':[r for r in rows if r['after'] is None],'patch_bytes':len(patch.encode())},ensure_ascii=False))
