"""Capture byte-frozen phase2 sources and reuse the already executed identical baseline."""
from pathlib import Path
import datetime, hashlib, json, os
p=Path(__file__).resolve().parent;root=p.parents[4]
old=p.parent/'screen-current25-draft'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for line in (old/'SHA256SUMS').read_text().splitlines():
 h,name=line.split('  ',1);assert sha(old/name)==h
assert len((old/'SHA256SUMS').read_text().splitlines())==120
population=(old/'population.txt').read_bytes()
assert population==(p.parent/'review-final-source/screen-population-final-review.txt').read_bytes()
(p/'population.txt').write_bytes(population)
paths=population.decode().splitlines();assert len(paths)==len(set(paths))==25
prior=json.loads((old/'capture.json').read_text())
prior_by_path={r['path']:r for r in prior['files']}
adoption=p.parent/'phase2-adoption/receipt.json';adopt=json.loads(adoption.read_text())
assert adopt['base_passed_source']=='0d6b6f842a48be813dcde7fdfd2a1a161fab2383'
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad'
current={path:(wt/path).read_bytes() for path in paths}
for row in adopt['source_blobs']:
 assert hashlib.sha256(current[row['path']]).hexdigest()==row['after_sha256']
rows=[]
for path in paths:
 row={'path':path,'baseline_blob':prior_by_path[path]['baseline_blob']}
 data_by_label={'base':(old/'inputs/base'/(path+'.txt')).read_bytes(),
                'previous-head':(old/'inputs/head'/(path+'.txt')).read_bytes(),
                'head':current[path]}
 for label,data in data_by_label.items():
  dest=p/'inputs'/label/(path+'.txt');assert not dest.exists()
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
  row[label+'_sha256']=hashlib.sha256(data).hexdigest()
  row[label+'_bytes']=len(data)
 assert row['base_sha256']==prior_by_path[path]['base_sha256']
 assert row['previous-head_sha256']==prior_by_path[path]['head_sha256']
 row['changed_vs_API']=data_by_label['base']!=current[path]
 row['changed_vs_previous_screen_bytes']=data_by_label['previous-head']!=current[path]
 rows.append(row)
assert all((wt/path).read_bytes()==current[path] for path in paths)
for oldname,newname in [('base.out','base.out'),('base.json','reused-base-execution.json'),
                        ('head.out','previous-head.out'),('head.json','reused-previous-head-execution.json'),
                        ('capture.json','reused-original-capture.json'),('SHA256SUMS','reused-original-SHA256SUMS'),
                        ('copy-text-screen-v3.py.txt','copy-text-screen-v3.py.txt'),('pairdiff.py.txt','pairdiff.py.txt')]:
 (p/newname).write_bytes((old/oldname).read_bytes())
(p/'phase2-adoption-receipt.json').write_bytes(adoption.read_bytes())
assert (root/'scripts/copy-text-screen-v3.py').read_bytes()==(p/'copy-text-screen-v3.py.txt').read_bytes()
assert (root/'devtools/seyoon/pairdiff.py').read_bytes()==(p/'pairdiff.py.txt').read_bytes()
receipt={'captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'label':'Actual frozen phase2; uncommitted at captured time, final pushed-head linkage pending',
 'current_worktree':str(wt),'prior_passed_source_commit_from_root_receipt':adopt['base_passed_source'],
 'baseline_commit':prior['base_commit'],'baseline_execution_reused_not_rerun':True,
 'baseline_original_commit_and_blob_verification_receipt':'reused-original-capture.json',
 'old_120_entry_manifest_verified':True,'old_folder_untouched':True,
 'phase2_adoption_receipt_sha256':sha(adoption),'count':25,
 'current_sources_stable_during_capture':True,'files':rows}
(p/'capture.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'count':25,'capture_sha256':sha(p/'capture.json'),
 'changed_vs_API':sum(r['changed_vs_API'] for r in rows),
 'changed_vs_previous_screen_bytes':sum(r['changed_vs_previous_screen_bytes'] for r in rows),
 'source_capture_complete_and_stable':True},indent=2))
