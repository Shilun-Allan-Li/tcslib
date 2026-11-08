"""Own closed-LOCAL artifact review. No reviewed imports or native execution."""
from pathlib import Path
from collections import Counter
import ast,datetime as dt,hashlib,json,re,subprocess

W=Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4');A=W/'.lake/ps-maintainer/gate06-combined-20261108'
P=A/'native-local-resume-r1';B=A/'native-bootstrap-resume-r1';R=A/'native-bootstrap-r1';TREE=A/'oleans-r1';OUT=A/'native-local-receipt-peer-r1'
RESULT_SHA='6a019e8051ef7deceae8fec3fd9ac53698e43985c7fe9f86d4e7b1d0ab12e656'
MANIFEST_SHA='1627b5d035e672e6c10f19ad693597ca373f6a25c48de84fdbb9291743e005be'
HEAD='a495f3953afff46ad5dec2d29ac8a7f55bd8ae37'
ENGINE_SHA='64b5b2ff2260a48eef55dcf77bdb5c4125459170b28c30499f60a93de7da3c95'
COORD_SHA='24731171b60eb8da0ce731b633f60bc175c424d877e45fa357a0883d02ce83c5'
CHECKER_SHA='366dab40e8e8f0f13e14118e14c3d6be1bc1b36604e6c9ccdebb03bc96cdf335'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def need(t,m):
 if not t:raise AssertionError(m)
def lines(p):return [json.loads(s) for s in p.read_text().splitlines()]
def files(root,rows,extras):
 need(len(rows)==len({r['path'] for r in rows}),'unique manifest paths')
 need({p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}=={r['path'] for r in rows}|set(extras),'exact artifact set')
 for r in rows:
  p=root/r['path'];need(p.resolve(strict=True).is_relative_to(root) and not p.is_symlink() and p.stat().st_size==r['bytes'] and sha(p)==r['sha256'],'artifact bytes')
def main():
 started=dt.datetime.now(dt.timezone.utc).isoformat()
 need(not(A/'native-runner.lease.json').exists(),'wait for LOCAL lease release')
 need(not(P/'STOP.json').exists() and sha(P/'RESULT.json')==RESULT_SHA,'closed successful LOCAL pin')
 result=load(P/'RESULT.json');need(result['passed'] is True and result['phase']=='local-continuation' and result['head']==HEAD and result['coordinator_sha256']==COORD_SHA and result['engine_sha256']==ENGINE_SHA,'receipt producer/source')
 need(subprocess.check_output(['git','--no-optional-locks','rev-parse','HEAD'],cwd=W,text=True).strip()==HEAD,'current HEAD')
 need(sha(P/'FILE-MANIFEST.json')==result['file_manifest_sha256']==MANIFEST_SHA,'LOCAL manifest pin')
 manifest=load(P/'FILE-MANIFEST.json');files(P,manifest,{'FILE-MANIFEST.json','RESULT.json'})
 need(sha(B/'RESULT.json')==result['bootstrap_aggregate_sha256']=='e1fa6d0282b1e683f971a3e4088ec5e36228615b279634745e1ff4ea1ace8cca','BOOT receipt')
 br=load(B/'RESULT.json');need(sha(B/'FILE-MANIFEST.json')==br['file_manifest_sha256']=='f26e727bea498ad3287c5d928ccb09dce11b3e36bec1574b13f10d36880bc70c','BOOT manifest')
 files(B,load(B/'FILE-MANIFEST.json'),{'FILE-MANIFEST.json','RESULT.json'})
 inv=A/'native-runtime-parallel-r1/R1-FINGERPRINTS.json';need(sha(inv)==result['R1_input_manifest_sha256']=='47c3740c7e5abaf68fe9a82cdb0eba405ea9acdf51a7c14248a16b5817e7beaa','R1 inventory')
 files(R,load(inv)['files'],set());need(not(R/'RESULT.json').exists(),'old failed R1 never cleared')
 need(sha(A/'native-runtime-parallel-r1/continue_native.py')==COORD_SHA and sha(A/'native-runtime-proposal/run_combined_native.py')==ENGINE_SHA and sha(W/'scripts/lean_check_tree.sh')==CHECKER_SHA,'reviewed implementation bytes')
 need(sha(A/'user-rulings-20261108-r1.json')==result['execution_scope']['approval_sha256']=='3f0730086b324c2773bcf5239eadfdb86f7c026bbbb5bf2f344283372fa7f9fa','user policy')
 inventory=load(P/'source-start.json');need(inventory==load(P/'source-final.json')==load(B/'source-start.json') and len(inventory)==1109,'stable full source inventory')
 actual={p.relative_to(W).as_posix() for p in (W/'TCSlib').rglob('*.lean')}|{'TCSlib.lean','audits/pass-shelat/Checks.lean'}
 need(actual==set(inventory),'exact current source scope')
 for name,digest in inventory.items():need(sha(W/name)==digest,'current source byte')
 records=load(P/'local-records.json');ext=load(P/'external-final.json');modules=load(A/'native-prep/plan-r1/modules.json');modulemap={r['module']:r for r in modules}
 copy=load(A/'native-prep/plan-r1/copy-plan.json');copymap={r['module']:r for r in copy};order=(A/'native-prep/plan-r1/rebuild-order.txt').read_text().splitlines()
 need(len(records)==len(modulemap)==1075 and set(records)==set(modulemap) and len(copymap)==437 and len(order)==len(set(order))==638 and set(order).isdisjoint(copymap) and set(order)|set(copymap)==set(records),'exact1075=437+638')
 need(len(ext)==3810 and sum(v['kind']=='TOOLCHAIN_LEAF' for v in ext.values())==173,'3810 external metadata')
 positions={r['module']:i for i,r in enumerate(modules)}
 for name,r in records.items():
  s=modulemap[name];need(r['source_sha256']==s['source_sha256']==inventory[name+'.lean'],'module source link')
  need(set(r['direct_local_object_sha256'])==set(s['local_imports']) and all(positions[d]<positions[name] and r['direct_local_object_sha256'][d]==records[d]['object_sha256'] for d in s['local_imports']),'local direct dependency links/topology')
  need(r['direct_external_object_sha256']=={d:ext[d]['object_sha256'] for d in s['external_imports']},'external direct dependency metadata')
  if name in copymap:need(r['object_sha256']==copymap[name]['object_sha256'] and r['origin']=='G06_COPY_SUPPORTED_BY_THREE_EXACT_FRESH_REPRODUCTIONS','warm copy metadata')
  else:need(r['origin']=='FRESH_LOCAL_CONTINUATION','fresh local origin')
 hist=lines(P/'attempt-ledger.jsonl');boot=lines(B/'attempt-ledger.jsonl');success=load(P/'successes.json')
 need(hist[:len(boot)]==boot and len(boot)==37 and [r['key'] for r in hist[37:]]==['local:'+name for name in order],'full ordered bootstrap+638 ledger')
 need(len(hist)==len({r['id'] for r in hist})==675 and len(success)==674,'675 attempts/674 success identities')
 counts=Counter(r['status'] for r in hist);need(counts==result['history_status_counts']=={'PASSED_REUSED':2,'HOST_COLLISION_RETAINED':1,'PASSED_NEW':672},'actual outcome counts')
 need({r['key'] for r in hist if r['status'] in {'PASSED_REUSED','PASSED_NEW'}}==set(success),'exact success keys')
 source_cache={};root_rows={};failures=[];receipt_links=[]
 for item in hist:
  need(item['native_started'] is True,'all675 actual native attempts')
  rp=Path(item['record_path']);need(sha(rp)==item['record_sha256'],'receipt hash');r=load(rp);d=rp.parent
  raw=(d/'native.log').read_text();st=load(d/'start.json');child=load(d/'child.json')
  need(sha(d/'native.log')==item['log_sha256']==r['log_sha256'] and load(d/'end.json')==r,'log/end links')
  need(json.loads(raw.splitlines()[0])==st and json.loads(raw.splitlines()[-1])=={'event':'END','utc':r['end_utc'],'rc':r['rc'],'interrupted':r['interrupted']},'raw START/END')
  need(r['head']==st['head']==HEAD and r['module']==st['module'] and child['command']==['/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',r['module']] and child['pid']==child['pgid'] and child['runner_pid']>0,'native source/child identity')
  need(r['dependencies_before']==r['dependencies_after']==st['dependencies_before'],'before/after dependency receipt equality')
  for name,dep in r['dependencies_before']['local'].items():
   need(dep['object_sha256']==records[name]['object_sha256'] and dep['source_sha256']==records[name]['source_sha256'] and dep['object_path']==str(TREE/(name+'.olean')) and dep['resolved_import_path']==str((TREE/(name+'.olean')).resolve()),'native local prerequisite link')
  for name,dep in r['dependencies_before']['external'].items():
   need(all(dep[k]==v for k,v in ext[name].items()) and dep['resolved_import_path']==str(Path(ext[name]['object_path']).resolve()),'native external prerequisite metadata link')
  src=W/(r['module']+'.lean')
  if src not in source_cache:source_cache[src]=sha(src)
  need(r['source_sha256']==r['source_sha256_before']==r['source_sha256_after']==st['source_sha256']==source_cache[src] and r['source_unchanged'],'actual native source bytes')
  need(r['checker_sha256']==r['checker_sha256_after']==st['checker_sha256']==CHECKER_SHA and r['runner_sha256']==r['runner_sha256_after']==st['runner_sha256']==ENGINE_SHA,'native tool pins')
  need(r['error_diagnostics']==len(re.findall(r'\berror(?:\([^)]*\))?:',raw))==0,'zero source errors')
  ok=item['status'] in {'PASSED_REUSED','PASSED_NEW'};need(r['passed'] is ok,'raw outcome vs ledger')
  if ok:
   need(r['rc']==0 and r['interrupted'] is None and r['post_validation_error'] is None and r['fresh_nonempty_object'] is True and r['object_sha256'],'actual success')
   rss=re.search(r'^\s*(\d+)\s+maximum resident set size\s*$',raw,re.M);need(rss is not None and int(rss[1])==r['max_rss_bytes_macos'],'RSS metadata')
   if item['key'].startswith('local:'):need(r['object_sha256']==records[item['key'][6:]]['object_sha256'],'fresh local result hash link')
   if r['expected_reproduction_sha256']:need(r['object_sha256']==r['expected_reproduction_sha256'],'fresh reproduction exact bytes')
   if item['key']=='CacheProbe':need(raw.splitlines().count('G06-COMBINED-CACHE-383 EOF')==1,'cache EOF')
   if item['key']=='PFRIdentityProbe':need(len(re.findall(r'PFR-MODULE ([A-Za-z0-9_.]+): ([A-Za-z0-9_.]+)',raw))==31 and len(re.findall(r'PFR-MODULES 31; PFR-PRIVATE \d+; EOF',raw))==1,'owner probe markers retained')
  else:
   need(item['status']=='HOST_COLLISION_RETAINED' and r['rc']==-15 and r['object_sha256'] is None and not r['fresh_nonempty_object'] and r['post_validation_error']=="RuntimeError('Native checker failed')",'old failure retained')
   node=ast.parse(r['interrupted'],mode='eval').body;need(isinstance(node,ast.Call) and ast.unparse(node.func)=='RuntimeError','exact interruption shape')
   msg=ast.literal_eval(node.args[0]);prefix='HOST_COLLISION: another native operation started: ';need(msg.startswith(prefix),'host reason');foreign=json.loads(msg[len(prefix):]);need(foreign and all(x['pgid']!=child['pgid'] for x in foreign),'foreign group distinct');failures.append({'key':item['key'],'record_sha256':item['record_sha256'],'rc':r['rc'],'object_sha256':r['object_sha256']})
  receipt_links.append({'id':item['id'],'key':item['key'],'status':item['status'],'record_path':str(rp),'record_sha256':item['record_sha256'],'log_sha256':r['log_sha256'],'source_sha256':r['source_sha256'],'rc':r['rc'],'fresh_nonempty_object':r['fresh_nonempty_object'],'object_sha256':r['object_sha256']})
  if r['module'] in {'TCSlib','audits/pass-shelat/Checks'}:root_rows[r['module']]=r
 need(set(root_rows)=={'TCSlib','audits/pass-shelat/Checks'},'both final aggregate checks')
 root_objects=[]
 for name,r in root_rows.items():
  obj=TREE/(name+'.olean');need(obj.resolve(strict=True).is_relative_to(TREE) and obj.is_file() and obj.stat().st_size>0 and sha(obj)==r['object_sha256']==records[name]['object_sha256'],'current Root/Checks object hash')
  root_objects.append({'module':name,'rc':r['rc'],'error_diagnostics':r['error_diagnostics'],'fresh_nonempty_object':r['fresh_nonempty_object'],'object_sha256':sha(obj),'object_bytes':obj.stat().st_size,'source_sha256':r['source_sha256'],'log_sha256':r['log_sha256']})
 need(sha(P/'RESULT.json')==RESULT_SHA and sha(P/'FILE-MANIFEST.json')==MANIFEST_SHA,'closed inputs stable')
 report={'status':'CLOSED_LOCAL_ARTIFACT_AND_PROVENANCE_REVIEW_PASS_NO_NATIVE','review_started_utc':started,'review_ended_utc':dt.datetime.now(dt.timezone.utc).isoformat(),'source_head':HEAD,'LOCAL_result_sha256':RESULT_SHA,'LOCAL_manifest_sha256':MANIFEST_SHA,'LOCAL_manifest_files':len(manifest),'all675_receipt_source_log_directdep_links':len(receipt_links),'status_counts':dict(counts),'success_identities':len(success),'local_records':len(records),'warm_copy_metadata_records':len(copy),'fresh_local_successes':len(order),'external_metadata_records':len(ext),'source_inventory_files_currently_hashed':len(inventory),'R1_retained_failures':failures,'current_Root_Checks_objects':root_objects,'reviewed_programs_imported_or_executed':False,'native_executed':False,'limits':['All1075 record/direct-dependency metadata links reviewed; current byte hashes independently repeated only for Root/Checks objects, not remaining1073 local objects.','All3810 external objects/source records compared as metadata; their current object bytes were not independently rehashed. R3 guard/Root provides that separate verification.','Historical native outcomes are validated receipts, not checks rerun by this reviewer.','No Rule10 or merge clearance follows from ordinary native success.']}
 with (OUT/'validation.json').open('x') as f:json.dump(report,f,indent=2);f.write('\n')
 with (OUT/'all-attempt-links.json').open('x') as f:json.dump(receipt_links,f,indent=2);f.write('\n')
 print(json.dumps({'status':report['status'],'validation_sha256':sha(OUT/'validation.json'),'attempt_links_sha256':sha(OUT/'all-attempt-links.json'),'Root_Checks':root_objects},indent=2))
if __name__=='__main__':main()
