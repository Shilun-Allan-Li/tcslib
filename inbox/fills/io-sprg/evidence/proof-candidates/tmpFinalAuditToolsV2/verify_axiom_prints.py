# io-sprg diagnostic comparison, Mac host 2026-11-18. No Lean.
import argparse,json,re,hashlib,runpy
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('census');ap.add_argument('log');ap.add_argument('output');ap.add_argument('--inventory',required=True);ap.add_argument('--probe-binding',required=True);a=ap.parse_args()
iv=runpy.run_path(str(Path(__file__).with_name('checkpoint_inventory.py')));inv=iv['load'](a.inventory)
probe=json.loads(Path(a.probe_binding).read_text())
assert probe['head']==inv['head'] and probe['inventory_sha256']==inv['inventory_sha256']
assert probe['status']=='CURRENT_BOUND_PROBE_PASS' and probe['owners']==inv['owners']
assert Path(a.log).resolve()==Path(probe['log']).resolve() and hashlib.sha256(Path(a.log).read_bytes()).hexdigest()==probe['log_sha256']
prepared_path=Path(probe['prepared_binding']);assert hashlib.sha256(prepared_path.read_bytes()).hexdigest()==probe['prepared_binding_sha256']
assert hashlib.sha256((Path(inv['root'])/(probe['probe_module']+'.lean')).read_bytes()).hexdigest()==probe['probe_sha256'],'current archived probe source differs'
prepared=json.loads(prepared_path.read_text());assert prepared['head']==inv['head'] and prepared['inventory_sha256']==inv['inventory_sha256'] and prepared['probe_sha256']==probe['probe_sha256']
assert prepared['census_sha256']==hashlib.sha256(Path(a.census).read_bytes()).hexdigest()
assert not Path(a.output).exists(),'preserve historical comparison; choose fresh output'
rows=json.loads(Path(a.census).read_text());expected={r['name']:set(r['axioms']) for r in rows if r['kind']=='theorem' and not r['private'] and not r['internal']}
text=Path(a.log).read_text();got={}
pattern=r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for m in re.finditer(pattern,text,re.M):
 assert m[1] not in got,m[1];got[m[1]]=set(x.strip() for x in(m[2] or '').split(',') if x.strip())
assert set(got)==set(expected),(len(got),len(expected),set(expected)-set(got),set(got)-set(expected))
assert got==expected,{n:[sorted(got[n]),sorted(expected[n])] for n in got if got[n]!=expected[n]}
assert sorted(expected)==prepared['public_theorems'],'prepared print coverage differs'
Path(a.output).write_text(json.dumps(dict(head=inv['head'],inventory_sha256=inv['inventory_sha256'],environment_sha256=probe['environment_sha256'],census_sha256=hashlib.sha256(Path(a.census).read_bytes()).hexdigest(),probe_binding_sha256=hashlib.sha256(Path(a.probe_binding).read_bytes()).hexdigest(),printed_public_theorems=len(got),all_match_current_graph=True,log_sha256=hashlib.sha256(Path(a.log).read_bytes()).hexdigest()),indent=1)+'\n');print('AXIOM_PRINTS_MATCH',len(got))
