from pathlib import Path
import json,hashlib,re,subprocess
E=Path('/private/tmp/ab34-fe-live1-final-validation/evidence');F=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4')
def load(n):return json.loads((E/n).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
a=load('INPUT-895-before.json');b=load('INPUT-895-after.json');c=load('CLONE-895-before.json');d=load('OUTPUT-895.json');assert a==b;A={r['path']:r for r in a};C={r['path']:r for r in c};D={r['path']:r for r in d};assert set(A)==set(C)==set(D) and len(A)==895
order=(E/'replay-order.txt').read_text().splitlines();rows=load('REPLAY-RESULTS.json');assert len(order)==len(rows)==163;inside={m+'.olean' for m in order};outside=sorted(set(A)-inside);assert len(outside)==732
for p in outside:assert C[p]==D[p],p
for i,(m,r) in enumerate(zip(order,rows),1):
 assert r['module']==m and r['index']==i and r['PASS'] and r['fresh_object'] and r['errors']==0 and r['exit']==0
 assert sha(E/r['output_file'])==r['output_sha256'];assert sha(F/(m+'.lean'))==r['source_sha256'];assert r['object_after_sha256']==D[m+'.olean']['sha256']
for r in load('REPLAY-SOURCE-MAP.json'):assert sha(E/'replay-source'/(r['path']+'.txt'))==r['sha256']==sha(F/r['path'])
for r in load('RUN-HELPER-CAPTURE.json')['files']:assert sha(Path(r['path']))==r['sha256']
static=(E/'replay-static.txt').read_text();assert static.strip()=='modules 163, mismatches 0, static total 49'
assert (E/'replay.log').read_text().splitlines()[-1]=='# modules=163 failed=0'
H=load('SOURCE.json')['head'];assert subprocess.check_output(['git','--no-optional-locks','-C',str(F),'rev-parse','HEAD'],text=True).strip()==H;assert not subprocess.check_output(['git','--no-optional-locks','-C',str(F),'status','--porcelain','--untracked-files=no']).strip()
owners={r['path'][:-5] for r in load('SOURCE.json')['files']};ownerrows=[r for r in rows if r['module'] in owners];assert len(ownerrows)==5 and all(r['sorry_warnings']==0 for r in ownerrows)
res={'PASS':True,'modules':163,'fresh_objects':163,'errors':0,'failed':0,'inherited_static_total':49,'static_mismatches':0,'input895_unchanged_including_inode_mtime':True,'clone895_content_exact_input_with_independent_inodes':True,'outside732_unchanged_from_initial_clone_including_inode_mtime':True,'all163_raw_output_hashes_source_bytes_final_object_hashes_exact':True,'executed_driver_and_helper_hashes_unchanged':True,'final_owner_sketches_actual_compiled5':True,'all5_owner_sorry_warnings':0,'no_source_changes':True,'owners':[{'module':r['module'],'source_sha256':r['source_sha256'],'object_sha256':r['object_after_sha256'],'output_sha256':r['output_sha256']} for r in ownerrows]};(E/'REPLAY-VERIFICATION.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k!='owners'},indent=2))
