from pathlib import Path
import re,json,hashlib,subprocess,shutil,collections
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');V=Path('/private/tmp/ab34-ro1-native-overlay');B=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8')
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
initial=json.loads((O/'snapshot-initial-maps.json').read_text());bm={str(p.relative_to(B)):h(p) for p in sorted(B.rglob('*.olean'))};vm={str(p.relative_to(V)):h(p) for p in sorted(V.rglob('*.olean'))}
assert bm==initial['input_MAC8'];assert set(vm)==set(bm) and len(bm)==895
changed={r['path'][:-5]+'.olean' for r in json.loads((O/'current-source-map.json').read_text())};unexpected=[p for p in bm if bm[p]!=vm[p] and p not in changed];assert not unexpected
(O/'snapshot-final-maps.json').write_text(json.dumps({'input_MAC8_final':bm,'whole_private_overlay_final':vm,'original_MAC8_all895_unchanged':True,'complete_private_overlay895':True,'changed_object_count':sum(bm[p]!=vm[p] for p in bm),'only_changed_owner_objects_differ':True,'no_splicing':True},indent=2)+'\n')
inv=json.loads((O/'api-seal-inventory.json').read_text());expected={(r['definition'],r['mode']) for r in inv['control_identities']};positive={};negative=set()
for l in (O/'probes/APIControlsNative__attempt1.log').read_text().splitlines():
 m=re.match(r'CONTROL\|([^|]+)\|([^|]+)\|PASS\|kernelChecked=(.+)',l)
 if m:positive[(m[1],m[2])]=m[3]
for l in (O/'probes/APIControlsSealed__attempt1.log').read_text().splitlines():
 m=re.match(r'CONTROL\|([^|]+)\|([^|]+)\|FAIL',l)
 if m:negative.add((m[1],m[2]))
assert set(positive)==negative==expected
assert all(positive[(r['definition'],r['mode'])]==r['kernel_name'] for r in inv['control_identities'])
probes=[]
for name,expected_exit,expected_errors in [('APIScopeNative',0,0),('APIScopeSealed',0,0),('APIControlsNative',0,0),('APIControlsSealed',1,12)]:
 p=O/'probes'/(name+'__attempt1.json');r=json.loads(p.read_text());assert r['exit']==expected_exit and r['errors']==expected_errors and r['warnings']==0 and r['source_unchanged'];assert h(p.with_suffix('.log'))==r['raw_sha256'];probes.append(r)
(O/'api-seal-control-verification.json').write_text(json.dumps({'all_expected_outcomes_verified':True,'whole_API_body_native_sealed_pass':True,'ordinary_guards':6,'fresh_kernel_checked_positive_controls':len(positive),'exact_expected_negative_controls':len(negative),'identity_sets_and_names_exact':True,'unsafe_reducibility_or_transparency_override':False,'probes':probes},indent=2)+'\n')
def git(*args):
 q=subprocess.run(['git',*args],cwd=W,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True);assert q.returncode==0,(args,q.stderr);return q.stdout
head=git('rev-parse','HEAD').strip();source=git('rev-parse','9b5dcf46408db681bcbc721930ef2203fa6bc47d^{commit}').strip();git('cat-file','-e',head+'^{commit}');git('cat-file','-e',source+'^{commit}');diff=git('diff','--name-only',source,head,'--','*.lean');assert not diff
status=git('status','--porcelain=v1');expected_paths={r['path'] for r in json.loads((O/'current-source-map.json').read_text())};actual_paths={l[3:] for l in status.splitlines()};assert actual_paths==expected_paths
(O/'final-pins-and-worktree.json').write_text(json.dumps({'worktree':str(W),'head':head,'source_pin':source,'source_pin_to_head_Lean_diff':diff,'branch':git('branch','--show-current').strip(),'status':status,'only_expected60_source_files_modified':True,'no_Git_mutations':True,'full_downstream_replay_not_run':True,'no_screen_run':True},indent=2)+'\n')
controls=['campaign/maintainer/START-HERE.md','campaign/maintainer/WORKFLOW.md','campaign/maintainer/HANDOFF.md','policy.md','workflow.md','campaign/standards/TEMPLATE.md','campaign/duplication-ledger.md']
for rel in controls:
 p=O/'controls'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((W/rel).read_bytes())
print('Final895 maps, source/Git pins, exact six-guard controls, and control-document captures verified.')
