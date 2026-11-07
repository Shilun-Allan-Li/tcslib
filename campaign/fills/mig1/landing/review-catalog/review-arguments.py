"""Record tactic arguments for manual review; this is not a copy-text screen."""
from pathlib import Path
import json
import re
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
scope={'__file__':str(OUT/'freeze-check.py')}
script=(OUT/'freeze-check.py').read_text()
exec(compile(script.split("source=(OUT/'Catalog-current.lean.txt')")[0], 'balanced-freeze-helpers', 'exec'),scope)
chunks=scope['ns']['chunks'];split=scope['split'];code=scope['code']
defs=json.loads((OUT/'eligible-seal-v2.json').read_text())['definitions']
names={x['name'] for x in json.loads((OUT/'seal-inventory.json').read_text())['changed_proof_spans']}
records=[]
for file,selected in [('Catalog-current.lean.txt',names),('CodeSimulator-repaired.lean.txt',{'Turing.MachineFormat.canonPreserveInstall'})]:
    source=(OUT/file).read_text()
    for name,private,chunk in chunks(source):
        if name not in selected:continue
        header,body=split(chunk);assert body is not None
        start=source.index(chunk)+chunk.index(code(chunk))+len(header)+2
        for m in re.finditer(r'\b(rw|simp_all|simp|simpa|dsimp|unfold|change)\b',body):
            pos=start+m.start();line=source.count('\n',0,pos)+1
            tail=body[m.end():];a=re.match(r'\s*(?:only\s*)?\[',tail)
            args=None
            if a:
                off=a.end();depth=1;i=off
                while i<len(tail) and depth:
                    if tail[i]=='[':depth+=1
                    elif tail[i]==']':depth-=1
                    i+=1
                args=tail[off:i-1]
            elif m[1]=='unfold':args=tail.split('\n',1)[0]
            hits=[]
            if args:
                for d in defs+['Turing.embedEmitCfg']:
                    aliases={d,d.removeprefix('Turing.'),d.split('.')[-1]}
                    if any(re.search(r'(?<![\w.])'+re.escape(alias)+r'(?![\w.])',args) for alias in aliases):hits.append(d)
            records.append(dict(source=file,declaration=name,line=line,tactic=m[1],arguments=args,
                                foreign_symbol_mentions=hits,
                                line_text=source.splitlines()[line-1]))
candidates=[r for r in records if r['foreign_symbol_mentions']]
assert [(r['declaration'],r['line']) for r in candidates]==[('Turing.FinTM.computesFunInTime_splitSolve_spaceUsed',2399),('Turing.MachineFormat.canonPreserveInstall',1301)]
for r in records:
    r['direct_foreign_definition_unfold']=False
    r['manual_argument_disposition']='Published equation/lemma or same-home/local expression.'
for r in candidates:
    r['manual_argument_disposition']='Symbol occurs only as a term argument to Nat.add_mul / canonEmbedWords, not as an unfolding lemma argument. Guard also keeps it opaque.'
(OUT/'tactic-arguments.json').write_text(json.dumps(records,indent=2)+'\n')
(OUT/'tactic-arguments.txt').write_text('\n'.join(f"{r['source']}:{r['line']} {r['declaration']}\n{r['line_text']}\narguments: {r['arguments']}\n" for r in records))
print('Recorded',len(records),'tactic sites; two nested symbolic term mentions inspected; no direct foreign-definition unfolding argument found.')
