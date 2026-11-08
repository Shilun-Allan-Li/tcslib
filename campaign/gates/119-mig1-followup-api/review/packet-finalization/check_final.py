"""Independent final candidate integrity checks, reading only source/evidence."""
from pathlib import Path
import base64,hashlib,io,json,os,re,subprocess,tarfile
p=Path(__file__).resolve().parent;root=p.parents[4];gate=p.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest();env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
git=lambda *a:subprocess.run(['git','-C',str(root),*a],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env).stdout
base='3023dc1408c3d216fc07a7cbba9ae30135b861ed';head='f1ca767a10551960faf36ad9c8ff17bea3a2d88c'
# No existing earlier draft byte was rewritten.
old=p.parent/'packet-draft';m=json.loads((old/'MANIFEST.json').read_text())
for r in m['files']:
 b=(old/r['path']).read_bytes();assert len(b)==r['bytes'] and H(b)==r['sha256']
assert H((old/'MANIFEST.json').read_bytes())=='7bf20047354a5b750dae99a81f08987f9ec7e83729a8127c8c40c9311b3b0193'
# Actual source worktree remains precisely the pinned candidate; no tracking mutation here.
wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-followup')
wgit=lambda *a:subprocess.run(['git','-C',str(wt),*a],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env).stdout
assert wgit('rev-parse','HEAD').decode().strip()==head
assert not wgit('status','--porcelain','--untracked-files=no').strip()
pop=(gate/'review/source-lint-screen/population.txt').read_text().splitlines()
for f in pop:assert (wt/f).read_bytes()==git('show',head+':'+f)
# Reversible full16source archives are read as inert data, never extracted/executed.
archives=[]
for side,pin in [('base',base),('head',head)]:
 f=gate/'review/source-lint-screen'/(side+'.tar.base64.txt');enc=f.read_bytes();raw=base64.b64decode(b''.join(enc.split()),validate=True)
 with tarfile.open(fileobj=io.BytesIO(raw),mode='r:') as tf:
  regular=[]
  for member in tf.getmembers():
   assert not member.issym() and not member.islnk() and not member.name.startswith('/') and '..' not in Path(member.name).parts
   if member.isdir():continue
   assert member.isfile();regular.append(member.name);data=tf.extractfile(member).read();assert data==git('show',pin+':'+member.name)
  assert sorted(regular)==sorted(pop)
 archives.append({'endpoint':side,'encoded_bytes':len(enc),'encoded_sha256':H(enc),'raw_tar_bytes':len(raw),'raw_tar_sha256':H(raw),'all16regular_files_exact_Git_source':True,'no_extraction_or_execution':True})
text=(p/'pack.md').read_text();assert 'PENDING' not in text and '**DRAFT' not in text
assert all(x in text for x in ['3778','3782','2222','2228','401','77','272','state-only','T=0','arbitrary','1043','actual-branch-lean_check_tree.sh','shim','gate119-mig1-followup-api-findings.md'])
assert not list(p.rglob('*.lean'))
(p/'final-packet-QA.json').write_text(json.dumps({'prior_frozen7file_draft_manifest_unchanged':True,'actual_source_worktree_tracked_clean_and_exact_f1ca':True,'all16actual_source_bytes_exact_current_Git_head':True,'all32archived_source_bytes_exact_current_base_head':True,'full16source_tar_archives_independently_strict_decoded_and_compared':archives,'finalpack_no_pending_result_or_self_pin_field':True,'all_required_contract_edgecase_census_screen_replay_correction_fields_present':True,'no_active_lean_output':True,'scope':'Read-only source/evidence/packet QA, not another Lean/screen/replay run or audit verdict.'},indent=2)+'\n')
print('PASS: prior draft immutable; actualsource exact/clean;32source/2archive sides exact; finalpack current fields complete')
