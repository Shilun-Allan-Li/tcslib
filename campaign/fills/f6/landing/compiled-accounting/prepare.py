"""Prepare trusted import-only Hierarchy probes; no Git/source/snapshot operations."""
from pathlib import Path
import datetime,hashlib,json,os,tempfile
out=Path(__file__).resolve().parent;root=out.parents[4];H=lambda b:hashlib.sha256(b).hexdigest()
trusted=root/'campaign/gates/119-mig1-followup-api/review/compiled-comparison/Inventory.lean.txt';s=trusted.read_text();end=s.index('\n/-!')
s='import TCSlib.Complexity.SpaceComplexity.Hierarchy\n'+s[end:]
s=s.replace('every constant in all five owned modules','every constant owned by Hierarchy').replace('let owners : List Name := [`TCSlib.Complexity.TuringMachine.Finite,\n    `TCSlib.Complexity.TuringMachine.Encoding,\n    `TCSlib.Complexity.TuringMachine.Build.Wrappers,\n    `TCSlib.Complexity.TuringMachine.Build.Primitives,\n    `TCSlib.Complexity.TuringMachine.Build.Catalog]','let owners : List Name := [`TCSlib.Complexity.SpaceComplexity.Hierarchy]')
a=s.index('  let targets : List Name :=');b=s.index('  for home in owners do',a);s=s[:a]+'  let targets : List Name := [`Complexity.space_universal]\n'+s[b:]
s=s.replace('("typeExpr", toJson (reprStr ci.type)), ("unsafe", toJson ci.isUnsafe),','("typeExpr", toJson (reprStr ci.type)), ("valuePresent", toJson ci.value?.isSome),\n      ("unsafe", toJson ci.isUnsafe),')
s=s.replace('if targets.any (fun r => r.isPrefixOf n) then','if targets.any (fun r => r.isPrefixOf n) ||\n        (n.toString.splitOn ".f6_").length > 1 then')
s=s.replace('owners=5','owners=1')
for name in ['Inventory.lean.txt','Inventory-base.lean.txt','Inventory-head.lean.txt']:(out/name).write_text(s)
# Controls adapted only from maintainer-authored already executed trusted controls, not delivery.
c=(root/'campaign/fills/mig1/landing/followup119-consumer-proposal/Controls-native.lean.txt').read_text()
c=c.replace('import TCSlib.Complexity.TuringMachine.Build.Primitives','import TCSlib.Complexity.SpaceComplexity.Hierarchy').replace('attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n','').replace('mig119_consumer_controls','f6_fintype_controls').replace('MIG119ConsumerRflControl','F6FintypeRflControl')
a=c.index('  let names : List Name :=');b=c.index('  let mut index :=',a);c=c[:a]+'  let names : List Name := [`Turing.instFintypeRewindPhase, `Turing.instFintypeSeekPhase]\n'+c[b:]
a=c.index('            match resultType.getAppFn with');b=c.index('            match ← solve lhs rhs with',a)
c=c[:a]+'''            match resultType.getAppFn with
            | .const ``Fintype _ =>
              lhs := mkProj ``Fintype 0 lhs
              rhs := mkProj ``Fintype 0 rhs
            | _ => pure ()
'''+c[b:]
(out/'Fintype-controls-native.lean.txt').write_text(c)
guard='attribute [local irreducible] Turing.instFintypeRewindPhase Turing.instFintypeSeekPhase\n'
(out/'Fintype-controls-sealed.lean.txt').write_text(c.replace('\nset_option maxHeartbeats', '\n'+guard+'set_option maxHeartbeats',1))
probe='''import TCSlib.Complexity.SpaceComplexity.Hierarchy
set_option maxHeartbeats 0
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let home := `TCSlib.Complexity.SpaceComplexity.Hierarchy
  let some idx := env.getModuleIdx? home | throwError "owner import missing"
  let names : List Name := [`Turing.instFintypeRewindPhase, `Turing.instFintypeSeekPhase]
  for n in names do
    let some ci := env.find? n | throwError "missing instance {n}"
    let row := Json.mkObj [("name", toJson n.toString),
      ("typeExpr", toJson (reprStr ci.type)),
      ("valueExpr", toJson (ci.value?.map reprStr)),
      ("reducibility", toJson (reprStr (getReducibilityStatusCore env n))),
      ("instance", toJson (Meta.isInstanceCore env n)),
      ("private", toJson (isPrivateName n)), ("internal", toJson n.isInternalDetail)]
    logInfo m!"FINTYPEMETA|{row.compress}"
  let mut matches := 0
  for (n, ci) in env.constants.toList do
    if env.getModuleIdxFor? n != some idx then continue
    let tu := ci.type.getUsedConstants
    let vu := (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut found := false
    for target in names do
      if tu.contains target || vu.contains target then
        found := true
        logInfo m!"INSTUSE|{n}|{target}|inType={tu.contains target}|inValue={vu.contains target}"
    if found then
      matches := matches + 1
      let row := Json.mkObj [("name", toJson n.toString),
        ("typeExpr", toJson (reprStr ci.type)), ("valueExpr", toJson (ci.value?.map reprStr)),
        ("allDirectTypeConstantNames", toJson (tu.toList.map Name.toString)),
        ("allDirectValueConstantNames", toJson (vu.toList.map Name.toString))]
      logInfo m!"FINTYPEUSEVALUE|{row.compress}"
  logInfo m!"FINTYPECOMPLETE|{matches}"
'''
(out/'Fintype-witness-uses.lean.txt').write_text(probe)
wt=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/wt-f6');src=wt/'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean';data=src.read_bytes();assert H(data)=='8a44b4b35010ac116e34880269b80d1121d2fdd86166e62da75efeffc984c031'
receipt=json.loads((root/'campaign/fills/f6/landing/native1/result.json').read_text());assert receipt['exit']==0 and receipt['head']=='f72a807e2376a2b986675c992745d6affc23b96f' and receipt['source_sha256']==H(data)
project=Path(tempfile.mkdtemp(prefix='tcslib-f6-metadata-',dir='/private/tmp'));os.chmod(project,0o700)
toolchain=(wt/'lean-toolchain').read_bytes();assert toolchain.strip()==b'leanprover/lean4:v4.25.0';(project/'lean-toolchain').write_bytes(toolchain);(project/'.lake').mkdir();(project/'.lake/packages').symlink_to(wt/'.lake/packages',target_is_directory=True)
base_source=root/'campaign/fills/f6/review/final-2026-11-08/base-Hierarchy.lean.txt';assert H(base_source.read_bytes())=='1d7e0c7d706521991a623dfe6963650f867edfebe34c2dae8316e2078dc8069f'
rows=[]
for endpoint,name,source in [('base','oleans-mac4',base_source),('head','oleans-f6-native1',src)]:
 tree=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch')/name;ol=tree/'TCSlib/Complexity/SpaceComplexity/Hierarchy.olean';count=sum(1 for _ in tree.rglob('*.olean'));assert count==895
 rows.append({'endpoint':endpoint,'snapshot':str(tree),'complete_olean_count':count,'owner_olean':str(ol),'owner_olean_sha256':H(ol.read_bytes()),'source_path':str(source),'source_sha256':H(source.read_bytes())})
context={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'execution_authorized_by_parent_after_completed_native1':True,'candidate_head':'f72a807e2376a2b986675c992745d6affc23b96f','baseline_source_pin':'3023dc1408c3d216fc07a7cbba9ae30135b861ed','actual_worktree':str(wt),'actual_source_sha256':H(data),'probe_project':str(project),'toolchain':toolchain.decode().strip(),'native_preflight_receipt_sha256':H((root/'campaign/fills/f6/landing/native1/result.json').read_bytes()),'metadata_pattern_source':str(trusted.relative_to(root)),'metadata_pattern_sha256':H(trusted.read_bytes()),'snapshots_read_only':rows,'local_slot_budget':3,'machine_cap':5,'one_sequential_Lean_process':True,'no_Git_or_native_operation_by_preparation':True}
(out/'context.json').write_text(json.dumps(context,indent=2)+'\n')
print(json.dumps(context,indent=2))
