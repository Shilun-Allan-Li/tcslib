# io-sprg diagnostic comparison, Mac host 2026-11-18. No Lean.
import argparse,json,re,hashlib
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('census');ap.add_argument('log');ap.add_argument('output');a=ap.parse_args()
rows=json.loads(Path(a.census).read_text());expected={r['name']:set(r['axioms']) for r in rows if r['kind']=='theorem' and not r['private'] and not r['internal']}
text=Path(a.log).read_text();got={}
pattern=r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for m in re.finditer(pattern,text,re.M):
 assert m[1] not in got,m[1];got[m[1]]=set(x.strip() for x in(m[2] or '').split(',') if x.strip())
assert set(got)==set(expected),(len(got),len(expected),set(expected)-set(got),set(got)-set(expected))
assert got==expected,{n:[sorted(got[n]),sorted(expected[n])] for n in got if got[n]!=expected[n]}
Path(a.output).write_text(json.dumps(dict(printed_public_theorems=len(got),all_match_current_graph=True,log_sha256=hashlib.sha256(Path(a.log).read_bytes()).hexdigest()),indent=1)+'\n');print('AXIOM_PRINTS_MATCH',len(got))
