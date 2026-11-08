"""Supplement source freeze with top-level type-let handling, then image sweep."""
from pathlib import Path
import hashlib, json, re, sys

ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25-final79'
C=json.loads((OUT/'capture.json').read_text())
(OUT/'review-complete-headers.py').write_bytes(Path(__file__).read_bytes())
screen=(ROOT/'scripts/copy-text-screen-v3.py').read_text();sys.argv=['parser-only',C['temporary_trees']['head'],*C['population']]
h={};exec(compile(screen.split('decls = []')[0],'<canonical-v3-parser-helpers>','exec'),h)
def header(text):
    text=h['strip'](text).strip();depth=0;pending=0;i=0
    while i<len(text):
        ch=text[i]
        if ch in '([{⟨':depth+=1
        elif ch in ')]}⟩':depth-=1
        if depth==0:
            token=re.match(r'(?:letI|let)\b',text[i:])
            if token and (i==0 or not(text[i-1].isalnum() or text[i-1]=='_')):
                pending+=1;i+=len(token[0]);continue
            if text.startswith(':=',i):
                if pending:pending-=1;i+=2;continue
                return ' '.join(text[:i+2].split())
            if ch=='|' or (re.match(r'where\b',text[i:]) and (i==0 or not(text[i-1].isalnum() or text[i-1]=='_'))):return ' '.join(text[:i].split())
        i+=1
    return ' '.join(text.split())
controls=[
 ('theorem t (c : Cfg (input := x)) : c = c := by rfl','theorem t (c : Cfg (input := x)) : c = c :='),
 ('theorem t : let arg := [true]; arg = arg := by rfl','theorem t : let arg := [true]; arg = arg :='),
 ('theorem t : let a := let b := 0; b; a = a := by rfl','theorem t : let a := let b := 0; b; a = a :='),
 ('structure Example where\n  n : Nat','structure Example')]
for text,expected in controls:assert header(text)==expected
f=(ROOT/'devtools/seyoon/declfreeze.py').read_text();ns={};exec(compile(f.split('a = chunks(open(sys.argv[1]).read())')[0],'<canonical-declfreeze-helpers>','exec'),ns);ns['stmt']=header
freeze=[]
for path in C['population']:
    sides={side:{name:dict(private=private,text=text,header=header(text)) for name,private,text in ns['chunks']((OUT/'inputs'/side/(path+'.txt')).read_text())} for side in ['base','head']}
    a,b=sides['base'],sides['head'];changed=[dict(name=k,base=a[k]['header'],head=b[k]['header']) for k in sorted(a.keys()&b.keys()) if a[k]['header']!=b[k]['header']]
    visibility=[k for k in a.keys()&b.keys() if a[k]['private']!=b[k]['private']]
    pubA={k for k,r in a.items() if not r['private']};pubB={k for k,r in b.items() if not r['private']}
    assert not changed and not visibility and pubA==pubB,path
    let_headers=[dict(name=k,header=b[k]['header']) for k in sorted(b) if re.search(r'\blet(?:I)?\b',b[k]['header'])]
    freeze.append(dict(path=path,all_common_headers_identical=True,all_public_names_visibility_identical=True,top_level_type_let_headers=let_headers,
        private_added=sorted(k for k in b.keys()-a.keys() if b[k]['private']),private_removed=sorted(k for k in a.keys()-b.keys() if a[k]['private'])))
report=dict(method='Canonical namespace/anonymous-instance chunks; bracket-aware delimiter additionally skips top-level let/letI initializer assignments in result types. Four Python delimiter controls passed. Source-only text comparison, not a Lean parser or compiled/type census.',
    all25_common_headers_public_names_visibility_preserved=True,files=freeze,
    previous_limit='This is the primary79 source-header check, with nested-default and top-level result-type let handling. Historical63 parser artifacts remain separate; this is not a compiled census.')
(OUT/'source-freeze-complete-headers.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')

public_text=(OUT/'inputs/head/TCSlib/Complexity/TuringMachine/Composition.lean.txt').read_text()
public=next(t for n,priv,t in ns['chunks'](public_text) if n.endswith('.exists_comp_on_image'))
def signature(hd):return re.sub(r'^(?:private\s+)?(?:lemma|theorem)\s+\S+\s*','',hd).replace(' ','')
results=[]
for path in C['changed_files']:
    for name,private,chunk in ns['chunks']((OUT/'inputs/head'/(path+'.txt')).read_text()):
        hd=header(chunk);norm=hd.replace(' ','')
        hooks=sorted(set(re.findall(r'\b(?:[A-Za-z0-9_]+\.)*(?:exists_comp_on_image|bufferedComp[A-Za-z0-9_]*|bufferedSecondCfg_run|[A-Za-z0-9_]*comp_on_image|clNative_image)\b',chunk)))
        shape='FinTMBool' in norm and 'ComputesFunInTime' in norm and 'ComputesInTime' in norm and '∃' in norm
        # Short name, avoiding the broad Complexity namespace accidentally matching "comp".
        short=name.split('.')[-1];named=bool(re.search(r'image|_comp$|compos',short,re.I))
        if hooks or shape or named:
            results.append(dict(path=path,name=name,header=hd,shape_candidate=shape,hooks=hooks,private=private,
                exact_raw_signature_after_name_visibility_whitespace=signature(hd)==signature(header(public)),source=chunk,source_sha256=hashlib.sha256(chunk.encode()).hexdigest()))
exact=[r for r in results if r['exact_raw_signature_after_name_visibility_whitespace']]
assert {r['name'] for r in exact}=={'Complexity.sat_comp_on_image','Complexity.taut_comp_on_image'}
for row in results:
    name=row['name']
    if name=='Complexity.taut_comp_on_image':
        assert 'FinTM.exists_comp_on_image' in row['source']
        disposition='Same raw contract, NOW a direct public citation after the mechanical79 repair. Header/name/budget preserved; the duplicated raw implementation is removed in the candidate and retires on merge. This source-only check is not another Lean elaboration.'
    elif name=='Complexity.sat_comp_on_image':
        assert 'exists_comp_on_image' in row['source']
        disposition='Same raw contract, ALREADY a direct citation of FinTM.exists_comp_on_image. Retain compatibility name/header; no repair needed for this member.'
    elif name=='Complexity.clNative_image':
        disposition='Different CLASS-level polynomial packaging: second machine correct only on f image with budget measured at |f x|. Already uses published bufferedCompTM computation fact; remaining witness/majorant packaging is not the same raw existential contract, not covered automatically by seven retention kinds, and not proved an unavoidable new API.'
    elif any(s.endswith('.exists_comp_on_image') for s in row['hooks']):
        disposition='Inline call ALREADY uses the public raw on-image existential theorem; surrounding client arithmetic/computation is not another implementation of that raw theorem.'
    elif 'FinTM.bufferedComp_start' in row['hooks'] or 'FinTM.bufferedSecondCfg_run' in row['hooks']:
        raise AssertionError('Additional raw reconstruction hook needs inspection: '+name)
    elif any('bufferedCompTM_computesInTime' in s for s in row['hooks']):
        disposition='Already applies published operational buffered-composition computation result in a client machine/class proof. No second matching raw existential reconstruction found in this source block.'
    else:
        disposition='Client use of sat_comp_on_image, taut_comp_on_image or clNative_image, rather than a separate raw-contract rederivation; full source retained for inspection.'
    row['disposition']=disposition
out=dict(head=C['head'],touched_files=C['changed_files'],public_statement=header(public),public_home='TCSlib/Complexity/TuringMachine/Composition.lean',
    method='All five full sources: literal operational/image hooks, complete depth-aware signature shape, client call and inline closing inspection. Raw rg output retained separately. Candidate enumeration plus inspection, not a semantic exhaustiveness claim.',
    exact_raw_contract_members=2,new_raw_rederivations_eligible_for_mechanical_repoint=0,candidates=results,
    no_Lean_or_source_changes=True)
(OUT/'on-image-sweep-final.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
lines=['# Bounded five-file raw on-image contract sweep','','Public canonical: `Turing.FinTM.exists_comp_on_image` in the already included Composition home.','The raw contract fixes arbitrary M,U,f,g,T1,T2; image-only hU uses T2(|x|); result is','an existential N computing g with the exact budget2*T1+T2+2.','', '| Member | Complete raw contract? | Disposition |','|---|---|---|']
for row in results:lines.append('| `'+row['name']+'` | '+('yes' if row['exact_raw_signature_after_name_visibility_whitespace'] else 'no')+' | '+row['disposition']+' |')
lines+=['','Two exact raw-contract members were found; both now cite the public theorem.','Tautology was mechanically re-pointed in79; its name, header and budget are preserved.','No matching raw reconstruction remains in these bounded candidates. This task edited no source.','CounterLoop and SingleTape contain no candidate raw on-image closing under these hooks','or complete signature shapes. All five files and all candidate bodies are retained.','', 'Hardness.clNative_image is a different class-level image premise/majorant wrapper.','Its direct clients are not counted as new raw composition implementations. The seven','accepted debt kinds do not grant a new image-closure acknowledgment or API decision.','This is bounded candidate enumeration plus source inspection. No compiled consumer,','rule-10 seal, axiom check, replay, global semantic absence claim or gate clearance is made.']
(OUT/'on-image-sweep-final.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(complete_headers='PASS',type_let_headers=sum(len(r['top_level_type_let_headers']) for r in freeze),raw_signature_members=[r['name'] for r in exact],eligible_repoint=None,candidate_blocks=len(results)),indent=2))
