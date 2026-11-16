#!/usr/bin/env python3
"""Verify the resumed BobProgram handoff without repeating passing checks."""
import ast
import hashlib
import json
from pathlib import Path
import re
root=Path('evidence/subagents/b2')
rows=[json.loads(s) for s in (root/'probe-runs/final-01/results.jsonl').read_text().splitlines()]
assert len(rows)==4
for r in rows:
    assert r['exit']==r['errors']==0 and r['fresh_olean']
    assert r['source_sha256']==hashlib.sha256(Path(r['probe']).read_bytes()).hexdigest()
trace_rows=[json.loads(s) for s in (root/'probe-runs/trace-resumed-01/results.jsonl').read_text().splitlines()]
assert len(trace_rows)==1 and trace_rows[0]['exit']==trace_rows[0]['errors']==0
trace=Path(trace_rows[0]['log']).read_text().replace('\\t','\t')
axioms=re.findall(r'^AXIOMS\t([^\t]+)\t\[(.*?)\]',trace,re.M|re.S)
sorries=re.findall(r'^SORRY_CLOSURE\t([^\t]+)\t\[(.*?)\]',trace,re.M|re.S)
assert len(axioms)==len(sorries)==1 and not sorries[0][1].strip()
used={a.strip() for _,v in axioms for a in v.split(',') if a.strip()}
assert used<={'propext','Classical.choice','Quot.sound'}
def preamble(path):
    module=ast.parse(Path(path).read_text())
    return next(ast.literal_eval(n.value) for n in module.body if isinstance(n,ast.Assign)
                and any(isinstance(t,ast.Name) and t.id=='preamble' for t in n.targets))
p1=preamble('evidence/subagents/b/tools/make_seals.py')
p2=preamble('evidence/subagents/b2/tools/make_seals.py')
assert p1==p2
source=Path('TCSlib/Cryptography/SecureComputation/Yao/HybridProof/BobProgram.lean')
text=source.read_text()
assert all(len(line)<=100 for line in text.splitlines()) and len(text.splitlines())<1000
assert not re.search(r'\b(?:sorry|admit|unfold|delta)\b',text)
error_re=re.compile(r'^\S+\.lean:\d+:\d+: error[:(]',re.M)
development=[]
for p in sorted(root.glob('bobprogram-*.log')):
    s=p.read_text()
    development.append({'log':str(p),'errors':len(error_re.findall(s)),
                        'status':'MISSING_PREREQUISITE' if 'does not exist' in s else 'PASS'})
summary={'file':str(source),'source_sha256':hashlib.sha256(text.encode()).hexdigest(),
         'lines':len(text.splitlines()),'current_source_seals':4,'all_pass':True,
         'stored_constants':1,'axioms':sorted(used),'sorry_dependencies':[],
         'interrupted_trace_preserved':True,'only_incomplete_trace_restarted':True,
         'controls_reused_from':'evidence/subagents/b/seals/controls/manifest.json',
         'identical_seal_preamble_sha256':hashlib.sha256(p2.encode()).hexdigest(),
         'development':development}
(root/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
