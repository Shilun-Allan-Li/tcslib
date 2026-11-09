from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,os,subprocess,sys,time
O=Path('/private/tmp/ab34-small-gate-drafts');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=O/'metadata-project';S=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch');sc=json.loads((O/'scope.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def replay(item):
 for name in item['replay_candidates']:
  d=Path('/private/tmp/ab34-'+name+'-replay');p=d/'RESULT.json'
  if not p.exists():continue
  r=json.loads(p.read_text())
  if not r.get('pass'):continue
  assert r['head']==item['head'] and r['failed']==0 and r['static_exit']==0 and r['snapshot_valid'] and r['source_unchanged_during_replay'] and r['complete_output_objects']==895
  q=json.loads((d/'request.json').read_text());assert q['head']==item['head'] and q['snapshot_lean_commit']==sc['base'];tree=Path(q['output']);objects=json.loads((d/'output.json').read_text());assert len(objects)==895
  owner=item['owner'];before=json.loads((d/'source-before.json').read_text());assert before[owner]['sha256']==item['source_freeze']['rows'][0]['HEAD_sha256'];obj=owner[:-5]+'.olean';assert objects[obj]==sha(tree/obj)
  return {'folder':str(d),'RESULT':r,'request':q,'snapshot':str(tree),'owner_olean_sha256':objects[obj]}
 return None
def run(item,side,binding):
 gate=item['gate'];d=O/str(gate)/'metadata';d.mkdir(exist_ok=True);receipt=d/(side+'-run.json')
 if receipt.exists():
  old=json.loads(receipt.read_text())
  if old['exit']==0:return
  raise RuntimeError('Preserve failed probe and correct under a distinct attempt name: '+str(receipt))
 tree=Path(binding['snapshot']) if side=='HEAD' else S/'oleans-mac8';source=P/('Gate'+str(gate)+'SelectedMetadata.lean');log=d/(side+'.log');request=d/(side+'-request.json');owner_obj=item['owner'][:-5]+'.olean';obj_before=sha(tree/owner_obj);b=source.read_bytes()
 req={'gate':gate,'PR':item['pr'],'side':side,'source_pin':item['head'] if side=='HEAD' else item['base'],'owner':item['owner'],'roots':item['roots'],'source_probe_sha256':hashlib.sha256(b).hexdigest(),'snapshot':str(tree),'complete_snapshot_owner_object_before_sha256':obj_before,'matching_passing_head_replay':binding if side=='HEAD' else None,'scope':'Only the selected roots full type/universes/module/privacy/kind/simp/AX metadata; no proof values or massive owner inventory','no_pp_width':True};request.write_text(json.dumps(req,indent=2)+'\n')
 cmd=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(P),str(tree),source.name];env=dict(os.environ);env['TCSLIB_LEAN_SLOTS']='3';start=datetime.now(timezone.utc).isoformat();t=time.monotonic()
 with log.open('wb') as f:q=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
 raw=log.read_bytes();rs=[json.loads(l.split('|',1)[1]) for l in raw.decode(errors='replace').splitlines() if l.startswith('ABI|')];aux=[json.loads(l.split('|',1)[1]) for l in raw.decode(errors='replace').splitlines() if l.startswith('TYPE_AUX|')];complete=[l for l in raw.decode(errors='replace').splitlines() if l=='COMPLETE|'+str(len(item['roots']))]
 errors=len(re.findall(rb'\berror(?:\([^)]*\))?:',raw));warnings=raw.count(b'warning:');r={'gate':gate,'side':side,'source_pin':req['source_pin'],'snapshot':str(tree),'started_utc':start,'seconds_including_slot_wait':time.monotonic()-t,'command':cmd,'exit':q.returncode,'errors':errors,'warnings':warnings,'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'probe_source_sha256':req['source_probe_sha256'],'probe_source_unchanged':source.read_bytes()==b,'snapshot_owner_object_unchanged':sha(tree/owner_obj)==obj_before,'roots_expected':len(item['roots']),'roots_observed':len(rs),'complete_marker_exact':len(complete)==1,'one_own_helper_slot_local3_machine5_j4_nice10':True,'no_source_snapshot_or_Git_mutations':True};receipt.write_text(json.dumps(r,indent=2)+'\n');(d/(side+'-selected.json')).write_text(json.dumps({'roots':rs,'private_type_auxiliaries':aux},indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({k:r[k] for k in ['gate','side','exit','errors','warnings','roots_observed','seconds_including_slot_wait']}),flush=True)
 if q.returncode or errors or len(rs)!=len(item['roots']) or not r['complete_marker_exact']:raise RuntimeError('selected metadata failed; raw logs preserved')
for item in sc['items']:run(item,'BASE',{})
for item in sc['items']:
 b=replay(item)
 if b:run(item,'HEAD',b)
 else:print('HEAD_PENDING_MATCHING_PASSING_RESULT gate='+str(item['gate']),flush=True)
