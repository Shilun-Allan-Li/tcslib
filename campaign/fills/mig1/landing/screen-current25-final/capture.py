"""Capture the intended final 25-file source generation and reuse the pinned baseline/phase2 screen."""
from pathlib import Path
import datetime, hashlib, json, os
p=Path(__file__).resolve().parent;root=p.parents[4];old=p.parent/'screen-current25-phase2'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for line in (old/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1);assert sha(old/name)==h
assert len((old/'SHA256SUMS').read_text().splitlines())==136
population=(old/'population.txt').read_bytes();(p/'population.txt').write_bytes(population)
paths=population.decode().splitlines();assert len(paths)==len(set(paths))==25
prior=json.loads((old/'capture.json').read_text());prior_by_path={r['path']:r for r in prior['files']}
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad';current={path:(wt/path).read_bytes() for path in paths}
primitive='TCSlib/Complexity/TuringMachine/Build/Primitives.lean'
assert hashlib.sha256(current[primitive]).hexdigest()=='72226a291b0c7e9189883a0ebd75a88ca49bb1f19d0487e54316e542b847ee71'
assert all(hashlib.sha256(current[path]).hexdigest()==prior_by_path[path]['head_sha256'] for path in paths if path!=primitive)
rows=[]
for path in paths:
 row={'path':path,'baseline_blob':prior_by_path[path]['baseline_blob']}
 data_by_label={'base':(old/'inputs/base'/(path+'.txt')).read_bytes(),
                'previous-head':(old/'inputs/head'/(path+'.txt')).read_bytes(),'head':current[path]}
 for label,data in data_by_label.items():
  target=p/'inputs'/label/(path+'.txt');assert not target.exists()
  target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
  row[label+'_sha256']=hashlib.sha256(data).hexdigest();row[label+'_bytes']=len(data)
 assert row['base_sha256']==prior_by_path[path]['base_sha256']
 assert row['previous-head_sha256']==prior_by_path[path]['head_sha256']
 row['changed_vs_API']=data_by_label['base']!=current[path]
 row['changed_vs_phase2']=data_by_label['previous-head']!=current[path]
 rows.append(row)
assert all((wt/path).read_bytes()==current[path] for path in paths)
for oldname,newname in [('base.out','base.out'),('reused-base-execution.json','reused-base-execution.json'),
                        ('head.out','previous-head.out'),('head.json','reused-previous-head-execution.json'),
                        ('capture.json','reused-previous-capture.json'),('SHA256SUMS','reused-previous-SHA256SUMS'),
                        ('reused-original-capture.json','reused-original-capture.json'),
                        ('pushed-head-linkage.json','previous-pushed-head-linkage.json'),
                        ('copy-text-screen-v3.py.txt','copy-text-screen-v3.py.txt'),('pairdiff.py.txt','pairdiff.py.txt')]:
 (p/newname).write_bytes((old/oldname).read_bytes())
assert (root/'scripts/copy-text-screen-v3.py').read_bytes()==(p/'copy-text-screen-v3.py.txt').read_bytes()
assert (root/'devtools/seyoon/pairdiff.py').read_bytes()==(p/'pairdiff.py.txt').read_bytes()
receipt={'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'label':'Intended final source; captured after third tagged-driver repoint, pushed-head linkage pending at capture time',
 'current_worktree':str(wt),'baseline_commit':prior['baseline_commit'],
 'previous_source_commit':'429bdd596adc15f229a8a03993967e5941cc2442',
 'baseline_and_phase2_executions_reused_not_rerun':True,'previous136_entry_manifest_verified':True,
 'previous_folder_untouched':True,'count':25,'current_sources_stable_during_capture':True,'files':rows}
(p/'capture.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'count':25,'capture_sha256':sha(p/'capture.json'),
 'changed_vs_API':sum(r['changed_vs_API'] for r in rows),'changed_vs_phase2':sum(r['changed_vs_phase2'] for r in rows),
 'source_capture_complete_and_stable':True},indent=2))
