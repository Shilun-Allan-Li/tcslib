from pathlib import Path
import json,hashlib,subprocess,os,datetime
out=Path(__file__).resolve().parent;root=out.parents[4]
wt=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4')
scratch=Path(os.environ['TCSLIB_SCRATCH']);base='1160c18f03fd318f0dec25738790935fa61379d4'
env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
git=lambda *a:subprocess.run(['git','-C',str(wt),*a],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,env=env).stdout
assert git('cat-file','-t',base).strip()==b'commit'
preflight=json.loads((root/'campaign/gates/119-mig1-followup-api/evidence/preflight/receipt.json').read_text())
assert preflight['failures']==0 and preflight['modules']==5
H=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for r in preflight['runs']:
 rel=r['source'];actual=(wt/rel).read_bytes();assert H(actual)==r['source_sha256']
 old=git('show',base+':'+rel);stem=Path(rel).stem
 (out/(stem+'-base.lean.txt')).write_bytes(old);(out/(stem+'-head.lean.txt')).write_bytes(actual)
 row={'file':rel,'base_source_sha256':H(old),'head_source_sha256':H(actual),'head_matches_actual_preflight':True}
 for mode,tree in [('base',scratch/'oleans-mra2'),('head',scratch/'oleans-mfollowup-preflight')]:
  op=tree/Path(rel).with_suffix('.olean');row[mode+'_olean_path']=str(op);row[mode+'_olean_sha256']=H(op.read_bytes())
 rows.append(row)
for mode in ['base','head']:(out/('Inventory-'+mode+'.lean.txt')).write_bytes((out/'Inventory.lean.txt').read_bytes())
context={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'worktree':str(wt),'baseline_commit':base,'candidate_head_at_capture':git('rev-parse','HEAD').decode().strip(),'base_snapshot':str(scratch/'oleans-mra2'),'head_snapshot':str(scratch/'oleans-mfollowup-preflight'),'scope':'Read-only import-only native census/AX; no Lean source/compiled-tree mutation, no integrated/replay execution by this agent.','source_and_olean_pins':rows,'preflight_receipt_sha256':H((root/'campaign/gates/119-mig1-followup-api/evidence/preflight/receipt.json').read_bytes()),'toolchain':(wt/'lean-toolchain').read_text().strip()}
(out/'context.json').write_text(json.dumps(context,indent=2)+'\n');print(json.dumps({'sources':len(rows),'head':context['candidate_head_at_capture'],'toolchain':context['toolchain']},indent=2))
