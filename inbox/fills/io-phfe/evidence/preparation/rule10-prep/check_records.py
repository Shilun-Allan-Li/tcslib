#!/usr/bin/env python3
"""Strict post-run install/EOF/component/mask checks; never invokes Lean or Git.
Use alongside canonical sealsum.py and ctlcheck2.py, not as a replacement.
"""
import argparse,importlib.util,json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--records',type=Path,required=True);ap.add_argument('--run',type=Path,required=True)
ap.add_argument('--tools',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
ap.add_argument('--controls',action='store_true');a=ap.parse_args()
p=a.tools/'seal/review/archived-gate10-tools/request_payload_adapter.py'
sp=importlib.util.spec_from_file_location('phfe_verify_adapter',p);adapter=importlib.util.module_from_spec(sp);sp.loader.exec_module(adapter)
results={}
for line in (a.run/'results.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'module' in r:
  assert r['module'] not in results,'Duplicate probe run; use a fresh run directory'
  results[r['module']]=r
if a.controls:
 records=json.loads(a.records.read_text())
else: records=[json.loads(p.read_text()) for p in sorted(a.records.glob('Seal*_*.json'))]
output=[]
for rec in records:
 module=rec['module'] if a.controls else rec['probe_module']; run=results.get(module)
 status={'module':module,'label':rec['label'],'requested':rec.get('requested',0),
         'verified_install':0,'verified_eof':0,'ok':False}
 try:
  assert run is not None,'Missing result record'
  text=(a.run/'mods'/(module.replace('/','_')+'.log')).read_text()
  errors=[int(m[1]) for m in re.finditer(r'^\S+\.lean:(\d+):\d+: error[:(]',text,re.M)]
  sealed=rec.get('sealed',True)
  if a.controls:
   for c in rec['controls']:
    actual=sum(c['start_line']<=n<=c['end_line'] for n in errors)
    expected=1 if sealed and c['negative'] else 0
    assert actual==expected,f'{c["control"]}: {actual} errors vs {expected}'
   assert all(any(c['start_line']<=n<=c['end_line'] for c in rec['controls']) for n in errors),'Stray error'
   assert run['rc']==(1 if sealed else 0),'Wrong return code'
  else: assert run['rc']==0 and not errors,'Seal source errors'
  if sealed:
   rows=rec['rows']; base=rec['label']
   labels=re.findall(r'G06-SEAL label=(\S+) requested=',text)
   assert labels and len(labels)==len(set(labels)),'Missing/duplicate install labels'
   requested=0
   for label in labels:
    assert label==base or label.startswith(base+'_part'),'Unexpected chunk label'
    match=re.search(r'G06-SEAL label='+re.escape(label)+r' requested=(\d+) active=(\d+) already_irreducible=(\d+) verified=(\d+)',text)
    assert match,'Malformed install summary'; n,active,already,verified=map(int,match.groups())
    assert n==verified==active+already,'Install count mismatch'
    eof=re.findall(r'G06-SEAL-END label='+re.escape(label)+r' requested=(\d+) verified=(\d+)',text)
    assert eof==[(str(n),str(n))],'Missing/duplicate/mismatched EOF summary'
    subset=rows if label==base else rows[(int(label.rsplit('_part',1)[1])-1)*200:int(label.rsplit('_part',1)[1])*200]
    assert len(subset)==n,'Chunk count mismatch'
    own='\n'.join(l for l in text.splitlines() if 'label='+label+' ' in l)
    adapter.verify_component_log(own,label,subset,('install','eof'))
    adapter.verify_mask_log(own,label,subset,('install','eof'))
    requested+=n
   assert requested==rec['requested'],'Total request mismatch'
   status['verified_install']=requested; status['verified_eof']=requested
  status['ok']=True
 except (AssertionError,RuntimeError,OSError,ValueError) as e:status['reason']=str(e)
 output.append(status)
summary={'status':'EXECUTED_AND_PARSED','all_ok':bool(records) and all(x['ok'] for x in output),
         'requested_records':sum(x['requested'] for x in output),
         'verified_install_records':sum(x['verified_install'] for x in output),
         'verified_eof_records':sum(x['verified_eof'] for x in output),'probes':output,
         'limits':'Controls also require canonical ctlcheck2 ALL_OK and complete source/control coverage.'}
a.out.write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='probes'}))
if not summary['all_ok']:raise SystemExit(1)
