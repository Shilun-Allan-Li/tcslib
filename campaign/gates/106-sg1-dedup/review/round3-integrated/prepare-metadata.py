from pathlib import Path
import json,re
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4]
old=ROOT/'campaign/gates/106-sg1-dedup/review/round2-current/probes/ModuleCensus.lean.txt'
base=old.read_text();imports='\n'.join(line for line in base.splitlines() if line.startswith('import '))+'\n'
mods=[line[7:] for line in imports.splitlines()];assert len(mods)==9
names=[]
for row in json.loads((ROOT/'campaign/gates/106-sg1-dedup/review/round3-closure-repairs/changes.json').read_text()):
 names.append({'source_name':row['name'],'owner':row['file'].removesuffix('.lean').replace('/','.')})
for row in json.loads((ROOT/'campaign/gates/106-sg1-dedup/review/round3-extra-repairs/changes-proposed.json').read_text()):names.append({'source_name':row['name'],'owner':'TCSlib.Complexity.CookLevin.Hardness'})
names.append({'source_name':'clA5Drop_native','owner':'TCSlib.Complexity.CookLevin.Hardness'})
assert len(names)==len({r['source_name'] for r in names})==16
(OUT/'combined16.json').write_text(json.dumps(names,indent=2)+'\n');(OUT/'original9-owners.txt').write_text('\n'.join(mods)+'\n')
# Row formats are the existing gate106 CONSTANT census and prior ROOT/PROOFAX/CITED/FOREIGNDEF.
root_code=imports+'''\nset_option maxHeartbeats 0
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let kenv := env.toKernelEnv
  let wantedOwners : List Name := OWNERS
  let wantedRoots : List (String × Name) := ROOTS
  for mod in wantedOwners do
    unless (env.getModuleIdx? mod).isSome do throwError "missing imported module {mod}"
  let kind := fun (ci : ConstantInfo) => match ci with
    | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
    | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
    | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    | .inductInfo _ => "inductive" | .quotInfo _ => "quotient"
  let owned := env.constants.toList.filterMap fun (n, ci) =>
    match env.getModuleIdxFor? n with
    | some i =>
      let owner := env.header.moduleNames[i.toNat]!
      if wantedOwners.contains owner then some (n, ci, owner) else none
    | none => none
  let mut roots : Array Name := #[]
  for (n, ci, owner) in owned do
    match n with
    | .str _ base =>
      if wantedRoots.contains (base, owner) then
        if !isPrivateName n then throwError "unexpected nonprivate repair root {n}"
        roots := roots.push n
    | _ => pure ()
  if roots.size != wantedRoots.length then throwError "Root count mismatch {roots.size}/{wantedRoots.length}"
  for n in roots.qsort Name.lt do logInfo m!"ROOT|{n}|private={isPrivateName n}"
  for (n, ci, owner) in owned.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    logInfo m!"CONSTANT {n} module={owner} kind={kind ci} private={isPrivateName n} internal={n.isInternalDetail}"
    if !(roots.any (fun r => r.isPrefixOf n)) then continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"PROOFAX|{n}|kind={kind ci}|{(axs.qsort Name.lt).toList}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    let mut seen : Array Name := #[]
    for c in used do
      if seen.contains c then continue
      seen := seen.push c
      match env.getModuleIdxFor? c, kenv.find? c with
      | some j, some info =>
        let foreignOwner := env.header.moduleNames[j.toNat]!
        if (`TCSlib).isPrefixOf foreignOwner then
          logInfo m!"CITED|{n}|{c}|{foreignOwner}|kind={kind info}|private={isPrivateName c}"
          if let .defnInfo di := info then
            let hint := match di.hints with
              | .abbrev => "abbrev" | .opaque => "opaque" | .regular _ => "regular"
            logInfo m!"FOREIGNDEF|{n}|{c}|{foreignOwner}|hints={hint}"
      | _, _ => pure ()
'''
owner_expr='['+', '.join('`'+m for m in mods)+']';roots_expr='['+', '.join('('+json.dumps(r['source_name'])+', `'+r['owner']+')' for r in names)+']'
root_code=root_code.replace('OWNERS',owner_expr).replace('ROOTS',roots_expr);(OUT/'Metadata-roots-census-v1.lean.txt').write_text(root_code)
whole_code=imports+'''\nset_option maxHeartbeats 0
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let wanted : List Name := OWNERS
  let owned := env.constants.toList.filterMap fun (n, ci) =>
    match env.getModuleIdxFor? n with
    | some i =>
      let owner := env.header.moduleNames[i.toNat]!
      if wanted.contains owner then some n else none
    | none => none
  for n in owned.toArray.qsort Name.lt do
    let ax ← liftCoreM <| Lean.collectAxioms n
    logInfo m!"ALLAX|{n}|{(ax.qsort Name.lt).toList}"
    if !isPrivateName n then logInfo m!"PUBLICAX|{n}|{(ax.qsort Name.lt).toList}"
'''
(OUT/'Metadata-whole9-axioms-v1.lean.txt').write_text(whole_code.replace('OWNERS',owner_expr))
old_runner=(ROOT/'campaign/gates/106-sg1-dedup/review/round3-prefix-repair/run-probe.py').read_text()
# Metadata must import the two newly compiled modules from this complete overlay.
old_runner=old_runner.replace("context['snapshot']","context['overlay']").replace('tcslib-g106-r3-prefix-','tcslib-g106-r3-imported-meta-')
(OUT/'run-metadata.py').write_text(old_runner)
print('Prepared existing-schema full9 census and16root/descendant metadata; whole9ALLAX separate.')
