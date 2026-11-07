"""Independent final source freeze; only inert copies and this review folder are written."""
from pathlib import Path
import sys,importlib.util,json,hashlib,re,difflib,collections
sys.dont_write_bytecode=True
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
spec=importlib.util.spec_from_file_location('parser',ROOT/'campaign/fills/mig1/review/checkpoint07-2026-11-07/compare-source.py');P=importlib.util.module_from_spec(spec);spec.loader.exec_module(P)
H=lambda s:hashlib.sha256(s.encode() if isinstance(s,str) else s).hexdigest()
def split_header(raw):
    """Balance binders; skip statement-local let assignments, including their indented by values."""
    c=P.clean(raw);stack=[];quoted=False;i=0;pending=0
    while i<len(c):
        ch=c[i]
        if quoted:
            if ch=='\\':i+=2;continue
            if ch=='"':quoted=False
        elif ch=='"':quoted=True
        elif ch in '([{⟨':stack.append(ch)
        elif ch in ')]}⟩':
            assert stack,(raw[:100],i)
            stack.pop()
        elif not stack:
            if re.match(r'(?:let|letI|have)\b',c[i:]) and (i==0 or not (c[i-1].isalnum() or c[i-1]=='_')):
                pending+=1
            if c.startswith(':=',i):
                if pending:
                    pending-=1
                    tail=c[i+2:];m=re.match(r'\s*by\b[^\n]*\n',tail)
                    if m:
                        line_start=c.rfind('\n',0,i)+1
                        indent=len(c[line_start:i])-len(c[line_start:i].lstrip())
                        j=i+2+m.end()
                        while j<len(c):
                            e=c.find('\n',j);e=len(c) if e<0 else e+1;line=c[j:e]
                            if line.strip() and len(line)-len(line.lstrip())<=indent:break
                            j=e
                        i=j;continue
                    i+=2;continue
                return raw[:i].rstrip(),':=',raw[i+2:].strip()
            if re.match(r'where\b',c[i:]) and (i==0 or c[i-1].isspace()):return raw[:i].rstrip(),'where',raw[i+5:].strip()
            if ch=='\n' and re.match(r'\n\s*\|',c[i:]):return raw[:i].rstrip(),'equations',raw[i:].strip()
        i+=1
    return raw.rstrip(),'none',''
# Header controls cover named assignments, statement lets, proof-valued lets, and nested assignments.
controls=[('theorem nested (h : P (input := x)) : True := by\n  trivial\n','True'),('private lemma body :\n    let B := existingMachine x\n    P B := by\n  exact h\n','P B'),('private lemma view :\n    let V : T := by\n      rw [shape]\n      exact t\n    P V := by\n  exact h\n','P V'),('theorem two :\n    let V : T := by\n      have h := p\n      exact t h\n    let n := f (input := x)\n    Q V n := by\n  exact z\n','Q V n')]
for text,ending in controls:
 h,d,b=split_header(text);assert h.endswith(ending) and d==':=' and b.startswith('by\n  '),(h,d,b)
P.header=lambda s:P.norm(split_header(s)[0])
def decls(text):
    result=[]
    for d in P.decls(text):
        raw=d['raw'];nextdoc=re.search(r'(?m)^/(?:--|-!)',raw)
        if nextdoc:raw=raw[:nextdoc.start()]
        raw=raw.rstrip()+'\n';head,delimiter,body=split_header(raw)
        prefix=''.join(text.splitlines(keepends=True)[:d['start']-1]);docstart=prefix.rfind('/--');docend=prefix.rfind('-/');doc=prefix[docstart:docend+2] if docstart>=0 and docend>docstart and not prefix[docend+2:].strip() else ''
        result.append(dict(d,raw=raw,doc=doc,header_raw=head,delimiter=delimiter,body=body,body_code=P.norm(P.clean(body)),code=P.norm(P.clean(raw))))
    return result
FILES=[r['path'] for r in json.loads((OUT/'capture.json').read_text())['files']]
STAGES={stage:{f:(OUT/'snapshots'/stage/(f+'.txt')).read_text() for f in FILES} for stage in ['api','producer','current']}
DECLS={stage:{f:decls(text) for f,text in tree.items()} for stage,tree in STAGES.items()}
def compare(oldstage):
    result={};all_add=[];all_remove=[];headers=[];defs=[];roots=[]
    for f in FILES:
        oldlist=DECLS[oldstage][f];newlist=DECLS['current'][f];a={d['name']:d for d in oldlist};b={d['name']:d for d in newlist};common=set(a)&set(b);proof=[];doc=[];header=[];definition=[]
        for n in sorted(common):
            x,y=a[n],b[n]
            if x['header_raw']!=y['header_raw'] or x['private']!=y['private'] or x['kind']!=y['kind']:
                header.append({'name':n,'private':y['private'],'before':x['header_raw'],'after':y['header_raw']});headers.append((f,n,y['private']))
            if x['body_code']!=y['body_code']:
                row={'name':n,'private':y['private'],'kind':y['kind'],'line':y['start'],'end':y['end'],'before_body_sha256':H(x['body']),'after_body_sha256':H(y['body'])}
                if y['kind'] in ['lemma','theorem']:proof.append(row);roots.append(dict(row,path=f,change='existing-proof'))
                else:definition.append(row);defs.append((f,n,y['private'],y['kind']))
            elif x['raw']!=y['raw'] or x['doc']!=y['doc']:doc.append({'name':n,'private':y['private'],'body_token_identical':True,'raw_changed':x['raw']!=y['raw'],'leading_doc_changed':x['doc']!=y['doc']})
        added=[d for d in newlist if d['name'] not in a];removed=[d for d in oldlist if d['name'] not in b]
        for d in added:
            all_add.append((f,d['name'],d['private'],d['kind']))
            if d['kind'] in ['lemma','theorem']:roots.append({'name':d['name'],'private':d['private'],'kind':d['kind'],'line':d['start'],'end':d['end'],'path':f,'change':'new-proof'})
        all_remove += [(f,d['name'],d['private'],d['kind']) for d in removed]
        oldkeep=[d['name'] for d in oldlist if d['name'] in common];newkeep=[d['name'] for d in newlist if d['name'] in common]
        imports=lambda s:[l for l in P.clean(s).splitlines() if l.startswith('import ')]
        attributes=lambda s:[l for l in P.clean(s).splitlines() if l.startswith('attribute ') or l.startswith('@[')]
        result[f]={'declarations_before':len(oldlist),'declarations_after':len(newlist),'public_counts':[sum(not d['private'] for d in oldlist),sum(not d['private'] for d in newlist)],'private_counts':[sum(d['private'] for d in oldlist),sum(d['private'] for d in newlist)],'added':[{'name':d['name'],'private':d['private'],'kind':d['kind']} for d in added],'removed':[{'name':d['name'],'private':d['private'],'kind':d['kind']} for d in removed],'surviving_relative_order_equal':oldkeep==newkeep,'header_changes':header,'definition_changes':definition,'proof_body_changes':proof,'doc_or_layout_only_changes':doc,'imports_before':imports(STAGES[oldstage][f]),'imports_after':imports(STAGES['current'][f]),'standalone_attributes_equal':attributes(STAGES[oldstage][f])==attributes(STAGES['current'][f])}
    return {'base_stage':oldstage,'comparisons':result,'all_added':all_add,'all_removed':all_remove,'all_header_changes':headers,'all_definition_changes':defs,'proof_roots':roots}
api=compare('api');producer=compare('producer')
(OUT/'api-to-current.json').write_text(json.dumps(api,indent=2)+'\n');(OUT/'producer-to-repairs.json').write_text(json.dumps(producer,indent=2)+'\n');(OUT/'header-controls.json').write_text(json.dumps({'passed':True,'cases':[{'input':s,'full_header':split_header(s)[0],'proof_body':split_header(s)[2]} for s,_ in controls]},indent=2)+'\n')
expected_add={'Turing.FinTM.pairMapSndTM','Turing.FinTM.pairMapSndTM_computes','Turing.FinTM.pairMapSndTM_spaceUsed'};expected_remove=set((ROOT/'campaign/fills/mig1/inputs/retired-public-names.txt').read_text().splitlines());assert {n for _,n,private,_ in api['all_added'] if not private}==expected_add
assert {n for _,n,private,_ in api['all_removed'] if not private}==expected_remove
assert not [(f,n) for f,n,private in api['all_header_changes'] if not private]
assert all(r['surviving_relative_order_equal'] for r in api['comparisons'].values())
assert {(Path(f).name,n) for f,n,_ in api['all_header_changes']}=={('TimeConstructible.lean','Complexity.counter_count'),('Loop.lean','Turing.FinTM.loopHost_contracts'),('Loop.lean','Turing.FinTM.loopHost_prepare')}
assert {(Path(f).name,n) for f,n,_ in producer['all_header_changes']}=={('Wrappers.lean','Turing.FinTM.timedReady_dispatch'),('Wrappers.lean','Turing.FinTM.timed_ledger')}
assert {(Path(f).name,n) for f,n,_,_ in api['all_definition_changes']}=={('Primitives.lean','Turing.FinTM.emitterP2SmallIndex'),('Primitives.lean','Turing.FinTM.emitterP2PairIndex')}
# Static admissions: all17 targets discharged; the original three RAM proof bodies unchanged.
targets=json.loads((ROOT/'campaign/fills/mig1/inputs/target-admissions.json').read_text());baseline_admissions=json.loads((ROOT/'campaign/fills/mig1/inputs/base-admissions.json').read_text());rows=[]
for target in baseline_admissions:
 f,n=target['path'],target['name'];a=next(d for d in DECLS['api'][f] if d['name']==n);b=next(d for d in DECLS['current'][f] if d['name']==n);initial=bool(re.search(r'\b(?:sorry|admit)\b',a['body_code']));final=bool(re.search(r'\b(?:sorry|admit)\b',b['body_code']));is_target=any(t['name']==n for t in targets);assert initial
 assert not final if is_target else final and a['body']==b['body']
 rows.append({'name':n,'path':f,'target':is_target,'api_admission':initial,'current_admission':final,'header_literal_equal':a['header_raw']==b['header_raw'],'residual_body_bytes_frozen':None if is_target else a['body']==b['body']})
remaining=[{'path':f,'name':d['name'],'line':d['start']} for f in FILES for d in DECLS['current'][f] if re.search(r'\b(?:sorry|admit)\b',d['body_code'])];assert len(remaining)==3
(OUT/'admissions.json').write_text(json.dumps({'targets17':rows[:17],'RAM3':rows[17:],'remaining_static':remaining,'source_only_not_axiom_execution':True},indent=2)+'\n')
# Frozen three export headers are compared with the gated contract data.
contract={d['name']:d for d in decls((ROOT/'campaign/fills/mig1/inputs/forwarding-map-contract.lean.txt').read_text())};current={d['name']:d for d in DECLS['current']['TCSlib/Complexity/TuringMachine/Build/Primitives.lean']};exports=[]
for n in sorted(expected_add):
 assert P.norm(contract[n]['header_raw'])==P.norm(current[n]['header_raw']),n
 exports.append({'name':n,'header_normalized_equal_gated_contract':True,'line':current[n]['start'],'proof_admission_free':not bool(re.search(r'\b(?:sorry|admit)\b',current[n]['body_code']))})
(OUT/'forwarding-contracts.json').write_text(json.dumps(exports,indent=2)+'\n')
summary={'public_added3':sorted(expected_add),'public_removed6':sorted(expected_remove),'public_header_changes':0,'producer_private_header_strengthenings':api['all_header_changes'],'repair_private_header_reexpressions':producer['all_header_changes'],'changed_executable_defs':api['all_definition_changes'],'proof_roots_vs_api':len(api['proof_roots']),'proof_roots_vs_producer':len(producer['proof_roots']),'per_file':{f:{'public':r['public_counts'],'private':r['private_counts'],'changed_proofs':len(r['proof_body_changes']),'new_proofs':sum(x['kind'] in ['lemma','theorem'] for x in r['added']),'doc_layout_only':len(r['doc_or_layout_only_changes'])} for f,r in api['comparisons'].items()}}
(OUT/'freeze-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
