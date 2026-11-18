#!/usr/bin/env python3
"""PHFE paired controls using pinned seal harness; prepare only, never invoke Lean.

Requires HEAD-bound bytes, completed canonical collector, native ReaderCatalog, and seals.
Keeps the inherited control-plan format consumed by canonical ctlcheck2.py.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, re, sys
from pathlib import Path
sys.dont_write_bytecode=True

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path); m=importlib.util.module_from_spec(spec)
 spec.loader.exec_module(m); return m

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for n in ['snapshot','collector-log','reader-log','seal-dir','tools','out','scratch']:
  ap.add_argument('--'+n,type=Path,required=True)
 ap.add_argument('--variant',choices=['strict-A','strict-B','coe-A','coe-B'],required=True)
 a=ap.parse_args(); s=json.loads((a.snapshot/'snapshot.json').read_text())
 binding=json.loads((a.snapshot/'head-binding.json').read_text())
 assert binding['source_bytes_equal_head'] and binding['head']==s['head_at_snapshot']
 assert binding['snapshot_sha256']==sha(a.snapshot/'snapshot.json')
 root=Path(s['root'])
 toolhash=json.loads((a.snapshot/'tool-fingerprints.json').read_text())['files']
 for name,digest in toolhash.items(): assert sha(a.tools/name)==digest, 'Tool drift: '+name
 a.out.mkdir(parents=True,exist_ok=True); a.scratch.mkdir(parents=True,exist_ok=True)
 assert a.scratch.is_relative_to(root), 'Canonical runner requires scratch probes under worktree'
 for p,r in s['files'].items(): assert sha(root/p)==r['sha256'], 'Source drift: '+p
 coverage=json.loads((a.snapshot/'controls-coverage.json').read_text())
 cat={}; reader_rows={}; reader_done=[]; native_defs=[]
 for line in a.collector_log.read_text().splitlines():
  if line.startswith('CAT '):
   r=json.loads(line[4:]); assert r['name']['display'] not in cat; cat[r['name']['display']]=r
 for logpath in [a.collector_log,a.reader_log]:
  markers=[json.loads(l[14:]) for l in logpath.read_text().splitlines() if l.startswith('PHFE_SNAPSHOT ')]
  assert markers==[{'head':binding['head'],'snapshot_sha256':binding['snapshot_sha256']}], str(logpath)
 assert cat and 'CAT-COUNT '  in a.collector_log.read_text(), 'Incomplete collector log'
 for line in a.reader_log.read_text().splitlines():
  if line.startswith('PHFE_READER '):
   r=json.loads(line[12:]); assert r['target'] not in reader_rows; reader_rows[r['target']]=r
  elif line.startswith('PHFE_READER_DONE '): reader_done.append(json.loads(line[17:]))
  elif line.startswith('PHFE_DEFINITION '): native_defs.append(json.loads(line[16:]))
 assert len(reader_done)==1 and reader_done[0]['requested']==sum(r['requested_pair'] for r in coverage['rows'])
 assert reader_done[0]['verified']==reader_done[0]['requested'], 'Reader validation incomplete'
 recs=[]
 for path in sorted(a.seal_dir.glob('Seal*_*.json')):
  r=json.loads(path.read_text()); assert r['rev']==binding['head']; recs.append(r)
 assert recs,'No complete seal records'
 arch=a.tools/'seal/review/archived-gate10-tools'
 bs=load(arch/'build_seals.py','phfe_control_bs')
 ctl=load(arch/'build_controls.py','phfe_control_ctl')
 adapter=load(arch/'request_payload_adapter.py','phfe_control_adapter'); adapter.configure_builders(bs,ctl)
 # Exactly the inherited actual-Name/instance-mask harness. No tool edits.
 original_seal=bs.seal_command
 def chunked_seal(label,rows,*,end):
  if len(rows)<=200:return original_seal(label,rows,end=end)
  return b''.join(original_seal(f'{label}_part{i//200+1}',rows[i:i+200],end=end)
                  for i in range(0,len(rows),200))
 bs.seal_command=chunked_seal
 plans=[]; prepared=[]; gaps=[]; groups={}
 for ordinal,row in enumerate(coverage['rows'],1):
  if not row['requested_pair']: continue
  name=row['name']; rr=reader_rows.get(name); meta=cat.get(name)
  if not rr or not rr.get('ok') or rr.get('reader')!=row['reader'] or not meta:
   gaps.append({'name':name,'reason':'Missing/invalid native target or reader'}); continue
  candidates=[r for r in recs if name in {x['spelling'] for x in r['rows']}]
  chosen=min(candidates,key=lambda r:(r['requested'],r['label'])) if candidates else None
  if chosen:
   key=('own-seal',chosen['label']); module=chosen['module']; rows=chosen['rows']
   parent_label=chosen['label']
  elif meta['abbrev'] and row['kind']=='abbrev':
   key=('alias-counterfactual',row['module']); module=row['module']; parent_label=None
   rows=[{'spelling':name,'home':meta['home']['display'],
          'name_components':meta['name']['components'],'home_components':meta['home']['components'],
          'instance':meta['instance'],'matcher':meta['matcher'],'abbrev':meta['abbrev'],
          'collector_reducibility':meta['status']}]
  else:
   gaps.append({'name':name,'reason':'No owned consumer request set contains target',
                'native_status':meta['status'],'abbrev':meta['abbrev']}); continue
  g=groups.setdefault(key,{'module':module,'parent':parent_label,'kind':key[0],
                          'rows':rows if chosen else [],'bodies':[]})
  if not chosen:g['rows']+=rows
  g['bodies'].append((ordinal,row,rr))
  prepared.append({'name':name,'reader':row['reader'],'kind':key[0],'native_status':meta['status'],
                   'parent_seal':parent_label,'positive_verified':None,'negative_verified':None})
 for group_no,((kind,_),g) in enumerate(sorted(groups.items()),1):
  rows=g['rows']; module=g['module']; homes=sorted({r['reader_home'] for _,_,r in g['bodies']
                                                if r.get('reader_home') and r['reader_home']!=module})
  for sealed in [False,True]:
   label=f'PHFECTL_{a.variant.replace("-","_")}_{group_no:04d}_'+('S' if sealed else 'U')
   raw=(f'import Lean\nimport {module}\n'+''.join('import '+h+'\n' for h in homes)+
        '\nset_option maxHeartbeats 0\nset_option maxRecDepth 65536\n'+
        'set_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n').encode()
   if sealed:raw+=bs.seal_command(label,rows,end=False)
   raw+=b'namespace PHFEControls\n\n'; controls=[]
   for ordinal,row,rr in g['bodies']:
    reader=row['reader'];name=row['name']
    for neg in [True,False]:
     cname=f'control_{ordinal:04d}_'+('negative' if neg else 'positive')
     proof='by\n    intros\n    rfl' if neg else '@'+reader
     body=f'theorem {cname} : type_of% (@{reader}) :=\n  {proof}\n'
     start=raw.count(b'\n')+1;raw+=body.encode()+b'\n'
     controls.append({'control':cname,'target':name,'negative':neg,'start_line':start,
                      'end_line':start+body.count('\n')-1})
   raw+=b'end PHFEControls\n'
   if sealed:raw+=bs.seal_command(label,rows,end=True)
   dest=a.scratch/(label+'.lean');dest.write_bytes(raw)
   (a.out/(label+'.lean.txt')).write_bytes(raw)
   plans.append({'label':label,'module':dest.relative_to(root).with_suffix('').as_posix(),
     'owner':module,'kind':kind,'sealed':sealed,'requested':len(rows) if sealed else 0,
     'rows':rows if sealed else [],'controls':controls,
     'expected_errors':[c['start_line'] for c in controls if c['negative']] if sealed else [],
     'source_targets':[r['name'] for _,r,_ in g['bodies']],
     'probe_sha256':hashlib.sha256(raw).hexdigest(),'source_head':binding['head'],
     'parent_seal_label':g['parent'],'verified':False,
     'limitation':'Forced opacity diagnostic group for canonical abbrev exclusions'
                  if kind!='own-seal' else None})
 (a.out/'controls-plan.json').write_text(json.dumps(plans,indent=2)+'\n')
 (a.out/'controls-order.txt').write_text('\n'.join(p['module'] for p in plans)+'\n')
 (a.out/'coverage.json').write_text(json.dumps({'status':'PREPARED_NOT_RUN','variant':a.variant,
   'source_head':binding['head'],'requested_pairs':sum(r['requested_pair'] for r in coverage['rows']),
   'prepared_pairs':len(prepared),'verified_pairs':0,'executed_pairs':0,'coverage_complete':False,
   'pairs':prepared,'gaps':gaps,'native_definitions':native_defs,
   'alias_counterfactual_pairs':sum(r['kind']=='alias-counterfactual' for r in prepared),
   'canonical_tool_sha256':{str(p.relative_to(a.tools)):sha(p) for p in sorted(a.tools.rglob('*.py'))},
   'snapshot_sha256':sha(a.snapshot/'snapshot.json'),'collector_log_sha256':sha(a.collector_log),
   'reader_log_sha256':sha(a.reader_log),'lean_processes_started':0},indent=2)+'\n')
 print(json.dumps({'status':'PREPARED_NOT_RUN','pairs':len(prepared),'gaps':len(gaps),'verified':0}))
 if gaps: raise SystemExit('Prepared partial plan; coverage gaps remain and must not be treated as PASS')

if __name__=='__main__': main()
