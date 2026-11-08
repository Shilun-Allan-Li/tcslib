from pathlib import Path
import subprocess,json,hashlib,tempfile,os,datetime
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
S=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch')
P=Path('/private/tmp/mig-post234-compiled-accounting')
B='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c'
H='e3ae4d5975c200c64af3dca810d4f35f4eefcce6'
def sh(a): return subprocess.check_output(a,cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
for rev in [B,H]:
 assert sh(['git','rev-parse',rev]).decode().strip()==rev
 subprocess.run(['git','cat-file','-e',rev+'^{commit}'],cwd=R,check=True)
prior=R/'campaign/fills/mig1/landing/compiled-comparison-final'
m=json.loads((prior/'MANIFEST.json').read_text())
for row in m['files']:
 b=(prior/row['path']).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'],row['path']
oldfiles=[{'path':str(q.relative_to(prior)),'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(prior.rglob('*'))if q.is_file()]
(P/'historical-accounting-before.json').write_text(json.dumps(oldfiles,indent=2)+'\n')
baseprobe=(prior/'base.lean.txt').read_text()
mods=[l[len('import '):]for l in baseprobe.splitlines()if l.startswith('import TCSlib.')]
assert len(mods)==12 and len(set(mods))==12
context=['TCSlib.Complexity.TuringMachine.Finite']
probe=(R/'campaign/fills/f6/landing/compiled-accounting-final/Inventory.lean.txt').read_text()
start=probe.index('set_option maxHeartbeats')
probe=probe[start:]
probe=probe.replace('let owners : List Name := [`TCSlib.Complexity.SpaceComplexity.Hierarchy]','let owners : List Name := ['+', '.join('`'+x for x in mods+context)+']')
probe=probe.replace('  let targets : List Name := [`Complexity.space_universal]\n','')
cut=probe.index('    if targets.any')
probe=probe[:cut]+'''  for n in [`Turing.pairDiagTM_spaceUsed, `Turing.FinTM.incFixedTM_spaceUsed,
      `Turing.MultiTapeTM.exists_first_entry_of_fixed, `Turing.MultiTapeTM.exists_first_halt,
      `Turing.FinTM.redirectTM_spaceUsedByTape] do
    unless env.contains n do throwError "missing approved current-context API {n}"
    logInfo m!"API_PRESENT|{n}"
  logInfo m!"COMPLETE|{entries.length}|primaryOwners=12|contextOwners=1"
'''
probe=''.join('import '+x+'\n'for x in mods+context)+'''import Lean
/-! Read-only full constant/type/attribute/axiom inventory. The twelve MIG owners form the
primary population; unchanged Finite is a separately reported API-context owner. Private,
internal and auxiliary constants are not filtered. No proof value is rendered. -/
'''+probe
assert 'reprStr ci.value' not in probe and 'VALUE_REPR' not in probe and 'TARGETTYPE' not in probe
(P/'Inventory.lean.txt').write_text(probe)
project=Path(tempfile.mkdtemp(prefix='tcslib-mig-post234-'))
(project/'lean-toolchain').write_text('leanprover/lean4:v4.25.0\n')
(project/'.lake').mkdir()
packages=S.parent/'tcslib-arora-barak-ch3-4/.lake/packages'
assert packages.is_dir()
os.symlink(packages,project/'.lake/packages')
(project/'Base.lean').write_text(probe)
snap=S/'oleans-mac5'
objects={str(q.relative_to(snap)):{'bytes':q.stat().st_size,'sha256':sha(q.read_bytes())}for q in sorted(snap.rglob('*.olean'))}
assert len(objects)==895
adopt=R/'campaign/status/2026-11-08-followup119-merge'
assert objects=={r['path']:{'bytes':r['bytes'],'sha256':r['sha256']}for r in json.loads((adopt/'snapshot-objects.json').read_text())}
(P/'snapshot-base-before.json').write_text(json.dumps(objects,indent=2)+'\n')
source_rows=[]
for label,rev in [('Base',B),('initial-head-not-final',H)]:
 for mod in mods+context:
  path=mod.replace('.','/')+'.lean';b=sh(['git','show',rev+':'+path]);dest=P/'source-captures'/label/(path+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
  source_rows.append({'stage':label,'source':rev,'owner':mod,'path':path,'bytes':len(b),'sha256':sha(b),'git_blob':sh(['git','rev-parse',rev+':'+path]).decode().strip()})
(P/'source-inputs-preparation.json').write_text(json.dumps(source_rows,indent=2)+'\n')
ctx={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'campaign_base':B,'initial_head_not_final':H,'HEAD_native_or_metadata_not_run':True,'primary_owners':mods,'context_owners':context,'base_snapshot':str(snap),'base_whole_snapshot_objects':895,'base_adoption_manifest_sha256':sha((adopt/'MANIFEST.json').read_bytes()),'project':str(project),'toolchain':'leanprover/lean4:v4.25.0','packages':str(packages.resolve()),'wrapper':str(R/'devtools/seyoon/leanelab.sh'),'wrapper_sha256':sha((R/'devtools/seyoon/leanelab.sh').read_bytes()),'probe_sha256':sha(probe.encode()),'historical_accounting_manifest_sha256':sha((prior/'MANIFEST.json').read_bytes()),'all_historical_manifest_entries_verified':len(m['files']),'all_historical_physical_files':len(oldfiles),'full_types':True,'attributes_measured':['kernelHints','reducibility','simp','unfold','protected','instancePriority','unsafe','partial'],'arbitrary_attribute_registry_reverse_membership_not_claimed':True,'no_theorem_proof_value_rendering':True,'plain_wrapper_no_snapshot_writes':True,'Lean_one_at_a_time':True,'local_slots':3,'machine_slots':5}
(P/'preparation.json').write_text(json.dumps(ctx,indent=2)+'\n')
print(json.dumps(ctx,indent=2))
