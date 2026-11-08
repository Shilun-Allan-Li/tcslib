from pathlib import Path
import json,hashlib,subprocess,re,datetime
O=Path('/private/tmp/f6-post234-context-review');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');P=R/'campaign/fills/f6/landing/compiled-accounting-final';M=R/'campaign/status/2026-11-08-followup119-merge';F=R/'campaign/fills/f6/landing/replay-mf63';c=json.loads((O/'refresh-context.json').read_bytes());j=lambda p:json.loads(p.read_bytes())
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*a):return subprocess.check_output(['git','-C',c['source_worktree'],*a])
def leans(pin):
 out={}
 for ln in git('ls-tree','-r',pin).decode().splitlines():
  a,p=ln.split('\t')
  if p.endswith('.lean'):out[p]=a.split()[2]
 return out
now=leans(c['source_head']);expected=leans(c['campaign_base']);component=leans(c['proof_component']);expected['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']=component['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'];assert expected==now
# Authenticate every finalized replay/adoption input and root-provided full manifest.
assert sha((F/'MANIFEST.json').read_bytes())=='4da1e19d6508fb9aa593d9e526b725e17a7a70bdd6b7e8dadbf153bdfa5b6515'
for folder in [F,M]:
 m=j(folder/'MANIFEST.json')
 for row in m['files']:
  b=(folder/row['path']).read_bytes();assert (len(b),sha(b))==(row['bytes'],row['sha256'])
# The committed adoption receipt is source-pinned to root's records receipt, not a prospective self-hash.
adopt='750987d674899d97db3c73c7278c891fa8772b40';assert git('rev-parse',adopt+'^{commit}').decode().strip()==adopt;git('cat-file','-e',adopt+'^{commit}')
for p in M.iterdir():
 if p.is_file():assert p.read_bytes()==git('show',adopt+':'+str(p.relative_to(R)))
assert leans(adopt)==leans(c['campaign_base'])
mac=j(M/'receipt.json');assert mac['merge']==c['campaign_base'] and mac['passed_PR_source']=='f1ca767a10551960faf36ad9c8ff17bea3a2d88c' and mac['object_count']==895 and mac['not_a_new_elaboration_or_splice']
r=j(F/'receipt.json');assert r['head']==c['source_head'] and r['campaign_base']==c['campaign_base'] and r['pipeline_exit']==r['failed']==r['error_rows']==r['static_mismatches']==r['static_total']==0 and r['modules']==2
assert (O/'root-replay-receipt.received.json').read_bytes()==(F/'receipt.json').read_bytes()
order=(F/'order-mf63.txt').read_text().splitlines();assert order==['TCSlib/Complexity/SpaceComplexity/Hierarchy','TCSlib/Complexity/SpaceComplexity']
rows=re.findall(r'^(\S+) exit=(\d+) errors=(\d+) sorry=(\d+)$',(F/'replay-mf63.log').read_text(),re.M);assert [x[0] for x in rows]==order and all(x[1:]==('0','0','0') for x in rows)
launch=[]
for ln in (F/'replay-mf63-launches.log').read_text().splitlines():
 m=re.fullmatch(r'pid=\d+ (?:-j4 )+(\S+)\.lean -o (\S+)\.olean',ln);assert m and m[2].endswith('/oleans-mf63/'+m[1]);launch.append(m[1])
assert launch==order and (F/'replay-mf63-static.txt').read_text()=='modules 2, mismatches 0, static total 0\n'
objects=j(F/'snapshot-objects.json');assert len(objects['input'])==len(objects['output'])==895 and set(objects['input'])==set(objects['output']);changed=[k for k in objects['input'] if objects['input'][k]!=objects['output'][k]];assert changed==objects['changed']==['TCSlib/Complexity/SpaceComplexity/Hierarchy.olean']
adoptrows={x['path']:{'bytes':x['bytes'],'sha256':x['sha256']} for x in j(M/'snapshot-objects.json')};assert objects['input']==adoptrows
# Recheck every complete snapshot object after all fresh sequential checks.
for x in c['snapshots']:
 t=Path(x['path']);after=[{'path':str(p.relative_to(t)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(t.rglob('*.olean'))];before=j(O/('snapshot-'+x['endpoint'].lower()+'-before.json'));assert before==after and len(after)==895
 (O/('snapshot-'+x['endpoint'].lower()+'-after.json')).write_text(json.dumps(after,indent=2)+'\n')
 m={y['path']:{'bytes':y['bytes'],'sha256':y['sha256']} for y in after};assert m==objects['input' if x['endpoint']=='Base' else 'output']
oldbefore=j(O/'previous-final-before.json');oldafter=[{'path':str(p.relative_to(P)),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(P.rglob('*')) if p.is_file()];assert oldbefore==oldafter and len(oldafter)==100;(O/'previous-final-after.json').write_text(json.dumps(oldafter,indent=2)+'\n')
assert git('rev-parse','HEAD').decode().strip()==c['source_head']==git('rev-parse','@{upstream}').decode().strip();assert git('status','--porcelain=v1','--untracked-files=no')==b''
# Exact unchanged scoped input source equivalence remains valid, with every guard before its full target.
native=(O/'fresh-validation/Owner-native.lean.txt').read_bytes();sealed=(O/'fresh-validation/Owner-sealed.lean.txt').read_bytes();source=(O/'Hierarchy-current.lean.txt').read_bytes();append=b'\n#print axioms Complexity.space_universal\n#print axioms Complexity.f6_seam\n#print axioms Turing.seamCompTM_step\n';assert native==source+append
meta=j(P/'scoped-seals-final/source-equivalence.json');line=b'attribute [local irreducible] '+' '.join(meta['guards']).encode()+b'\n';nosimp=b'attribute [-simp] '+' '.join(meta['nosimp']).encode()+b'\n';rec=sealed
for i in range(1,20):
 n=f'F6LandingSeal{i:02d}'.encode();prefix=b'section '+n+b'\n'+line+nosimp+b'\n';suffix=b'end '+n+b'\n';assert rec.count(prefix)==rec.count(suffix)==1;rec=rec.replace(prefix,b'',1).replace(suffix,b'',1)
assert rec==native
for f in ['Controls-native.lean.txt','Controls-sealed.lean.txt']:
 b=(O/'fresh-validation'/f).read_bytes();assert b'goal.mvarId!.refl' in b and b'allowUnsafeReducibility' not in b and b'withTransparency' not in b
res={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_head':c['source_head'],'campaign_base':c['campaign_base'],'actual_merged_Lean_tree_exact_campaign_plus_unchanged_Hierarchy':True,'all_1003_Lean_files_verified':len(now),'mac5_adoption_records_commit':adopt,'mac5_manifest_sha256':sha((M/'MANIFEST.json').read_bytes()),'mac5_whole_MFUP2_adoption_and_actual895_hashes_exact':True,'MF63_manifest_sha256':sha((F/'MANIFEST.json').read_bytes()),'MF63_exact2rows_2launches_static0_0':True,'whole895_transition_only_Hierarchy_changed':True,'both895_snapshots_all_objects_unchanged_after_fresh_checks':True,'all100_previous_final_artifacts_unchanged':True,'source_still_clean_and_pushed':True,'current19scopes_inverse_exact':True,'current_controls_default_MetaM_refl_no_override':True,'current_guard_population':'35ordinaryTCSlib+Nat.bits;14abbrev/projection+2ineffective regularFintype limits retained','no_F6_proof_API_or_design_change_required':True,'new25_screen_and_final_packet_binding_still_root_and_screen_owner':True,'no_Git_source_canonical_snapshot_or_old_evidence_mutation_by_this_task':True}
(O/'final-context-verification.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
