from pathlib import Path
import hashlib,json,re
b=Path('evidence/subagents/b4')
src=Path('TCSlib/Cryptography/SecureComputation/Yao/HybridProof/GateOccurrences.lean')
s=src.read_text()
err=re.compile(r'^\S+\.lean:\d+:\d+: error[:(]',re.M)
dev={p.name:len(err.findall(p.read_text())) for p in sorted(b.glob('gateoccurrences-*.log'))}
results=[]
for p in sorted((b/'probe-runs').glob('*/results.jsonl')):
    results.extend(json.loads(line) for line in p.read_text().splitlines())
trace=(b/'probe-runs/trace-02/AxiomsAndTrace.log').read_text().replace('\\t','\t')
axioms=re.findall(r'^AXIOMS\t([^\t]+)\t\[(.*?)\]',trace,re.M|re.S)
sorry=re.findall(r'^SORRY_CLOSURE\t([^\t]+)\t\[(.*?)\]',trace,re.M|re.S)
allowed={'propext','Classical.choice','Quot.sound'}
bad=[(n,v) for n,v in axioms if {x.strip() for x in v.split(',') if x.strip()}-allowed]
summary={'source':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
 'lines':len(s.splitlines()),'wide_lines':[i for i,x in enumerate(s.splitlines(),1) if len(x)>100],
 'admissions':re.findall(r'\b(?:sorry|admit|axiom)\b',s),
 'explicit_unfolds':re.findall(r'\b(?:unfold|delta)\b',s),
 'development_diagnostic_counts':dev,'probe_results':results,
 'stored_constants':re.findall(r'STORED_CONSTANTS (\d+)',trace),
 'axiom_rows':len(axioms),'nonstandard_axioms':bad,
 'sorry_closure_rows':len(sorry),'nonempty_sorry_closures':[(n,v) for n,v in sorry if v.strip()]}
(b/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='probe_results'},indent=2))
assert not summary['wide_lines'] and not summary['admissions'] and not summary['explicit_unfolds']
assert len(results)==10 and all(x['exit']==0 and x['errors']==0 and x['fresh_olean'] for x in results)
assert not bad and not summary['nonempty_sorry_closures']
