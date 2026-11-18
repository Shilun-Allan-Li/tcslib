#!/usr/bin/env python3
"""ROOT-ONLY dormant preparation driver for canonical A/B strict+coe generators.
Starts only Python generators and their read-only git-show calls. Never starts Lean.
"""
import argparse,hashlib,json,os,re,subprocess,sys
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
for n in ['snapshot','tools','collector-log','out']: ap.add_argument('--'+n,type=Path,required=True)
ap.add_argument('--scratch-rel',required=True); a=ap.parse_args()
s=json.loads((a.snapshot/'snapshot.json').read_text()); b=json.loads((a.snapshot/'head-binding.json').read_text())
assert b['source_bytes_equal_head'] and b['head']==s['head_at_snapshot']
assert b['snapshot_sha256']==hashlib.sha256((a.snapshot/'snapshot.json').read_bytes()).hexdigest()
root=Path(s['root'])
for p,r in s['files'].items(): assert hashlib.sha256((root/p).read_bytes()).hexdigest()==r['sha256'],p
mods=(a.snapshot/'modules.txt').read_text().splitlines()
text=a.collector_log.read_text(); cats=[];roots={};closures={};counts={}
markers=[json.loads(l[14:]) for l in text.splitlines() if l.startswith('PHFE_SNAPSHOT ')]
assert markers==[{'head':b['head'],'snapshot_sha256':b['snapshot_sha256']}], 'Collector snapshot mismatch' 
for line in text.splitlines():
 if line.startswith('CAT '):cats.append(json.loads(line[4:]))
 elif line.startswith('ROOT '):
  r=json.loads(line[5:]);roots[r['module']]=roots.get(r['module'],0)+1
 elif line.startswith('CLOSURE '):
  r=json.loads(line[8:]);closures[r['module']]=r['closure']
 elif line.startswith('MODULE '):
  m,n=line[7:].split(': stored ');assert m not in counts;counts[m]=int(n)
assert set(counts)==set(closures)==set(mods), 'Incomplete module closure/root census'
assert all(counts[m]==roots.get(m,0) for m in mods), 'Stored ROOT counts differ'
assert re.findall(r'^CAT-COUNT (\d+)$',text,re.M)==[str(len(cats))], 'CAT count mismatch'
toolhash=json.loads((a.snapshot/'tool-fingerprints.json').read_text())['files']
for name,digest in toolhash.items():
 assert hashlib.sha256((a.tools/name).read_bytes()).hexdigest()==digest, 'Tool drift: '+name
arch=a.tools/'seal/review/archived-gate10-tools'
for coe in [False,True]:
 for letter in ['A','B']:
  variant=('coe' if coe else 'strict')+'-'+letter
  directory=a.out/variant; directory.mkdir(parents=True,exist_ok=True)
  script=a.tools/'seal/review'/('mkseals_coe.py' if coe else 'mkseals_ab.py')
  env=dict(os.environ,SEAL_EVAL='1' if letter=='B' else '0',SEAL_CHUNK='200')
  cmd=[sys.executable,'-I',str(script),str(arch),str(a.collector_log),str(root),b['head'],
       str(directory),a.scratch_rel+'/'+variant,'Seal'+letter+'_',*mods]
  subprocess.run(cmd,check=True,env=env)
  manifest=json.loads((directory/'manifest.json').read_text())
  assert len(manifest['probes'])==len(mods)
  (directory/'order.txt').write_text('\n'.join(r['probe_module'] for r in manifest['probes'])+'\n')
  (directory/'STATUS.json').write_text(json.dumps({'status':'PREPARED_NOT_RUN','variant':variant,
     'canonical':variant=='coe-A','source_head':b['head'],
     'requested_records':sum(r['requested'] for r in manifest['probes']),
     'verified_install_records':0,'verified_eof_records':0,'lean_processes_started':0},indent=2)+'\n')
