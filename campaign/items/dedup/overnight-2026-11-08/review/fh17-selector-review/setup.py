from pathlib import Path
import json,subprocess,hashlib,shutil,datetime,os
O=Path(__file__).parent;W=Path('/Users/seyoonr/.codex/worktrees/ab34-epad/tcslib-arora-barak-ch3-4');D=Path('/private/tmp/ab34-fe-live1-final-validation/EXPORT/first-None-census');H='2c85a68a73f74b79ac19ab2f824a17ddf2432962'
def git(*a):return subprocess.check_output(['git','--no-optional-locks','-C',str(W),*a],text=True).strip()
assert git('rev-parse','HEAD')==H;assert not git('status','--porcelain','--untracked-files=no')
rows=json.loads((D/'DETERMINISTIC-FIRST-NONE.json').read_text());todo=[r for r in rows if r['id'] not in [9,18,19,33,76]];assert len(todo)==13
for r in todo:
 source=(W/r['path']).read_bytes();chunk=(D/r['block']).read_bytes();assert source.count(chunk)==1,(r['id'],'chunk changed');p=O/'source/START'/(r['path']+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(source);p=O/r['block'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(chunk)
for p in ['devtools/seyoon/leanelab.sh','devtools/seyoon/leanelab-o.sh','scripts/lean_check_tree.sh','lean-toolchain','lake-manifest.json','policy.md','workflow.md','campaign/standards/TEMPLATE.md']:
 d=O/'helpers'/p;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(W/p,d)
shutil.copytree(D,O/'source-census')
(O/'TASK.json').write_text(json.dumps({'source_head':H,'source_branch':git('branch','--show-current'),'baseline':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','source_worktree':str(W),'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'authority':'Parent expressly authorized13 existing-API mechanical selector re-points, including colleague FYI cases; no Git/full replay/canonical writes. One block then native check.','todo':todo,'original4_consumers':[r for r in rows if r['id'] in [9,18,19,33]],'canonical':next(r for r in rows if r['id']==76),'all17_plus_canonical_dispositions':rows,'new_API_import_statement_home_debt_permission':False},indent=2)+'\n');print('Captured13 exact initial chunks/11 owners at '+H)
