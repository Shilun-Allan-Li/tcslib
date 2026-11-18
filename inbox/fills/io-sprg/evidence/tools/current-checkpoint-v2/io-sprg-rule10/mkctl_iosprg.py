# io-sprg Mac Rule10 controls,2026-11-18. PREPARATION ONLY: never invokes Lean.
# Adapted from bb1-sim mkctl_bb1sim.py's assemble/covering-subset/plan conventions.
# Host paths: positional worktree replaces /home/user/fill/tcslib; probe/output dirs
# are explicit evidence paths. Existing reviewed seal payload/Name checks/mask retained.
# Body rows are io-sprg full-reader types, never inherited BB1 controls.
import argparse,hashlib,importlib.util,json,os,sys
from pathlib import Path
sys.dont_write_bytecode=True
ap=argparse.ArgumentParser();ap.add_argument('tools');ap.add_argument('sealdir')
ap.add_argument('worktree');ap.add_argument('probe_subdir');ap.add_argument('outdir')
ap.add_argument('--static-plan',required=True)
a=ap.parse_args();wt=Path(a.worktree).resolve();out=Path(a.outdir).resolve();out.mkdir(parents=True,exist_ok=True)
static=json.loads(Path(a.static_plan).read_text())
assert str(wt)==static['root'],'static inventory belongs to another worktree'
def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec)
 spec.loader.exec_module(mod);return mod
bs=load(Path(a.tools)/'build_seals.py','iosprg_control_seals')
ct=load(Path(a.tools)/'build_controls.py','iosprg_control_archive')
ad=load(Path(a.tools)/'request_payload_adapter.py','iosprg_control_adapter');ad.configure_builders(bs,ct)
chunk=int(os.environ.get('SEAL_CHUNK','256'))
if chunk:
 old=bs.seal_command
 def seal(label,rows,*,end):
  if len(rows)<=chunk:return old(label,rows,end=end)
  return b''.join(old(f'{label}_part{i//chunk+1}',rows[i:i+chunk],end=end)
   for i in range(0,len(rows),chunk))
 bs.seal_command=seal
# io-sprg Mac performance adaptation, 2026-11-18: exact reversible success transport.
# Host path: the copied local fast_records.py replaces retained MessageLog success records
# with IO.println of the same MessageData rendering. No guard, mask or request changes.
if os.environ.get('SEAL_FAST_LOG') == '1':
    fast = load(Path(__file__).with_name('fast_records.py'), 'iosprg_fast_records')
    fast.configure_builders(bs, ct)

recs=[json.loads(p.read_text()) for p in sorted(Path(a.sealdir).glob('Seal*_*.json'))]
assert recs,'no completed seal records'
assert len(recs)==len(static['owners']) and {r['module'] for r in recs}==set(static['owners']),'seal/static owner set differs'
source_hashes={r['file']:r['sha256'] for r in static['files']}
for r in recs:
 assert r['rev']==static['head'] and r['source_sha256']==source_hashes[r['source']],'seal/static revision or source differs'
letters=sorted({r['label'].split('_')[0][-1]for r in recs})
candidates=[];issues=[];excluded=[]
requested_all={x['spelling']for r in recs for x in r['rows']}
for row in static['controls']:
 if row['kind']=='abbrev':
  excluded.append(dict(row,reason='reducible abbreviation; canonical irreducible seal cannot install'))
 elif row['reader']:
  candidates.append(row)
 else:
  used=any(row['name']in r.get('term_readers',{}) for r in recs)
  if row['name'] not in requested_all:
   excluded.append(dict(row,term_used=used,reason='not a CAT ordinary definition; proof-valued instance has no observable body'))
  else:issues.append(dict(row,term_used=used,reason='active definition has no rfl reader; repair before controls'))
chosen={};coverage=[]
for ix,row in enumerate(candidates,1):
 target=row['name']
 for letter in letters:
  owners=[r for r in recs if r['label'].split('_')[0][-1]==letter
   and target in {x['spelling']for x in r['rows']}]
  if not owners:
   coverage.append(dict(target=target,letter=letter,status='NOT_REQUESTED_IN_ANY_OWNER'))
   continue
  rec=min(owners,key=lambda r:(len(r['rows']),r['label']));chosen.setdefault(rec['label'],(rec,[]))[1].append((ix,row))
  coverage.append(dict(target=target,reader=row['reader'],letter=letter,
   status='PREPARED_NOT_RUN',owner=rec['module'],requested=len(rec['rows']),
   term_used=any(target in r.get('term_readers',{})for r in recs)))
known={r['name']for r in static['controls']}
anonymous={}
for rec in recs:
 for r in rec['rows']:
  if r['instance'] and r['home'] in static['owners'] and r['spelling'] not in known:
   entry=dict(name=r['spelling'],home=r['home'],
    term_used=any(r['spelling'] in q.get('term_readers',{}) for q in recs),
    reason='generated/anonymous instance: not in named source inventory; manual classification required')
   if r['spelling'].endswith('._sizeOf_inst'):
    excluded.append(dict(entry,reason='compiler-generated SizeOf instance; remains sealed, not a source public API definition'))
   else:anonymous[r['spelling']]=entry
plan=[]
for rec,items in [chosen[k]for k in sorted(chosen)]:
 for sealed in [False,True]:
  label=('ControlS_'if sealed else'ControlU_')+rec['label'][4:]
  src=f'import Lean\nimport {rec["module"]}\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 65536\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n'.encode()
  if sealed:src+=bs.seal_command(label,rec['rows'],end=False)
  src+=(wt/'evidence/tools/io-sprg-rule10/reader_rfl_elaborator.lean.txt').read_bytes()
  src+=b'namespace StructuredSeedSensitivity\n\n';expect=[]
  for ix,row in items:
   for negative in [True,False]:
    name=f'ctl{ix:03d}'+('Negative'if negative else'Positive')
    proof='@(reader_rfl% (@'+row['reader']+'))' if negative else '@'+row['reader']
    body=f'theorem {name} : type_of% (@{row["reader"]}) :=\n  {proof}\n'
    start=src.count(b'\n')+1;src+=body.encode()+b'\n'
    expect.append(dict(control=name,target=row['name'],reader=row['reader'],negative=negative,
     start_line=start,end_line=start+body.count('\n')-1))
  src+=b'end StructuredSeedSensitivity\n\n'
  if sealed:src+=bs.seal_command(label,rec['rows'],end=True)
  dest=wt/a.probe_subdir/(label+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(src)
  (out/(label+'.lean.txt')).write_bytes(src)
  plan.append(dict(label=label,module=a.probe_subdir+'/'+label,owner=rec['module'],kind='own-seal',
   sealed=sealed,requested=len(rec['rows']) if sealed else 0,controls=expect,
   expected_errors=[c['start_line']for c in expect if c['negative']]if sealed else[],
   source_sha256=hashlib.sha256(src).hexdigest()))
(out/'controls-plan.json').write_text(json.dumps(plan,indent=1)+'\n')
(out/'coverage.json').write_text(json.dumps(dict(coverage=coverage,excluded=excluded,
 unresolved=issues+list(anonymous.values()),status='PREPARED_NOT_RUN'),indent=1)+'\n')
for sealed,name in [(False,'unsealed-order.txt'),(True,'sealed-order.txt')]:
 (out/name).write_text(''.join(p['module']+'\n'for p in plan if p['sealed']==sealed))
print(len(plan),'control probes;',len(candidates),'reader rows;',len(excluded),'unsealable abbreviations;')
print('UNRESOLVED classification:',len(issues)+len(anonymous),'(must review coverage.json; not passing evidence)')
assert not issues and not anonymous,'ACTIVE CONTROL COVERAGE GAP: see coverage.json'
