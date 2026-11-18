# io-sprg cluster audit helper. No Lean process: prepares a probe or checks recorded results.
# Root runs each prepared probe separately through serial slot-wrapped runner_full.py.
import argparse,hashlib,json,re,runpy,subprocess
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('action',choices=['prepare','check']);ap.add_argument('label');ap.add_argument('file',nargs='?');ap.add_argument('--allow-added',action='append',default=[]);ap.add_argument('--results-dir');a=ap.parse_args()
root=Path.cwd();out=root/'evidence/checks'/a.label;out.mkdir(parents=True,exist_ok=True);meta=out/'expected.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if a.action=='prepare':
 p=Path(a.file);code='\n'.join(runpy.run_path('evidence/tools/clash/clash_scan.py')['strip_code'](p.read_text()));stack=[];names=[]
 for l in code.splitlines():
  m=re.match(r'^(namespace|section)\s+(\S+)',l)
  if m:stack.append((m.group(1),m.group(2)));continue
  m=re.match(r'^end(?:\s+(\S+))?\s*$',l)
  if m:
   assert stack,(l,p);kind,name=stack.pop();assert not m.group(1) or m.group(1)==name,(l,name);continue
  m=re.match(r'^(?:protected )?(?:theorem|lemma)\s+(\S+)',l)
  if m:names.append('.'.join(n for k,n in stack if k=='namespace')+'.'+m.group(1))
 assert not stack,stack
 probe=Path('evidence/probes')/(a.label.replace('-','_')+'_Axioms.lean');probe.write_text('import '+str(p.with_suffix('')).replace('/','.')+'\n'+''.join('#print axioms '+n+'\n' for n in names));meta.write_text(json.dumps({'file':str(p),'source_sha256':sha(p),'names':names,'probe':str(probe),'probe_sha256':sha(probe)},indent=1)+'\n');Path('evidence/logs/proof-axioms-order.txt').write_text(str(probe.with_suffix(''))+'\n');print('PREPARED',a.label,len(names));raise SystemExit
m=json.loads(meta.read_text());p=Path(m['file']);assert sha(p)==m['source_sha256'];folder=Path(a.results_dir) if a.results_dir else Path('evidence/meta')/a.label;rows=[json.loads(l) for l in(folder/'results.jsonl').read_text().splitlines()];r=next(r for r in reversed(rows) if r.get('module')==str(Path(m['probe']).with_suffix('')));assert r['rc']==r['errors']==r['sorry']==0;assert r['source_sha256']==m['probe_sha256'];logpath=folder/'mods'/(r['module'].replace('/','_')+'.log');assert sha(logpath)==r['log_sha256'];log=logpath.read_text()
axioms={n:sorted(x.strip() for x in aa.split(',') if x.strip()) for n,aa in re.findall(r"^'([^\n]*)' depends on axioms: \[([^]]*)\]",log,re.M)}
for n in re.findall(r"^'([^\n]*)' does not depend on any axioms",log,re.M):axioms[n]=[]
assert set(axioms)==set(m['names']),(set(m['names'])-set(axioms));assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
for name,cmd in [('frozen-decls',['python3','-I','briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py','.','d10a560b34d58919bc1a5206ce66a444613f94c7',str(p)]),('style',['python3','-I','scripts/style_lint.py',str(p)]),('sk15',['python3','-I','evidence/tools/dev/sk15.py',str(p)])]:
 rr=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(out/(name+'.log')).write_text(rr.stdout);assert rr.returncode==0,(name,rr.stdout)
 if name=='frozen-decls':
  assert not re.search(r'^(CHANGED|REMOVED)',rr.stdout,re.M),rr.stdout
  added={l.split('\t')[2] for l in rr.stdout.splitlines() if l.startswith('ADDED\t')}
  assert added==set(a.allow_added),(added,a.allow_added)
s=p.read_text();assert len(s.splitlines())<=1000 and max(map(len,s.splitlines()))<=100
summary=dict(source_sha256=sha(p),lines=len(s.splitlines()),max_width=max(map(len,s.splitlines())),frozen_statements_unchanged=True,added_helpers=a.allow_added,public_theorems=len(axioms),all_standard_axioms=True,axioms=axioms);(out/'summary.json').write_text(json.dumps(summary,indent=1)+'\n');print('VERIFIED',a.label,len(axioms),'standard-only',summary['lines'],'lines')
