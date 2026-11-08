"""Read-only byte linkage of the captured 25 files to a parent-supplied pushed commit."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, sys
p=Path(__file__).resolve().parent
commit,branch=sys.argv[1:3]
assert re.fullmatch(r'[0-9a-f]{40}',commit)
assert re.fullmatch(r'[A-Za-z0-9_./-]+',branch) and not branch.startswith('-') and '..' not in branch
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-epad'
def git(*args):return subprocess.check_output(['git','-C',str(wt),*args])
assert git('rev-parse',commit+'^{commit}').decode().strip()==commit
git('cat-file','-e',commit+'^{commit}')
tracking='origin/'+branch
assert git('rev-parse',tracking+'^{commit}').decode().strip()==commit
capture=json.loads((p/'capture.json').read_text());rows=[]
for row in capture['files']:
 path=row['path'];blob=git('rev-parse',commit+':'+path).decode().strip()
 assert re.fullmatch(r'[0-9a-f]{40}',blob)
 git('cat-file','-e',blob+'^{blob}')
 data=git('show',commit+':'+path)
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob
 assert hashlib.sha256(data).hexdigest()==row['head_sha256']
 assert data==(p/'inputs/head'/(path+'.txt')).read_bytes()
 rows.append({'path':path,'git_blob':blob,'sha256':row['head_sha256'],'byte_equal':True})
result={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'commit':commit,
 'parent_supplied_pushed_branch':branch,'local_remote_tracking_ref':tracking,'local_tracking_ref_matches':True,
 'remote_network_query_performed':False,'push_success_attested_by':'parent maintainer',
 'full_commit_and_25_full_blob_objects_verified':True,'all_25_source_bytes_equal':True,
 'extra_tiling_runs':0,'scope':'Exact captured25 source linkage; not a whole-tree freeze/replay or independent network push verification.',
 'files':rows}
assert not(p/'pushed-head-linkage.json').exists()
(p/'pushed-head-linkage.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
