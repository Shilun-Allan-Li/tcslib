from pathlib import Path
import json,re,os
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');P=O/'native-project';P.mkdir(exist_ok=True)
(P/'.lake').mkdir(exist_ok=True)
if not (P/'.lake/packages').exists():(P/'.lake/packages').symlink_to(W/'.lake/packages',target_is_directory=True)
(P/'lean-toolchain').write_bytes((W/'lean-toolchain').read_bytes())
freeze=json.loads((O/'declaration-freeze.json').read_text())
roots=[{'path':r['path'],'name':r['name']} for r in freeze['changed_proof_roots']+freeze['new_declarations']]
imports=''.join('import '+r['path'][:-5].replace('/','.')+'\n' for r in json.loads((O/'current-source-map.json').read_text()))+'import Lean\nset_option maxHeartbeats 0\n'
ax='''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : List (String × String) := ROOTS
  for (owner, sourceName) in roots do
    let hits := env.constants.toList.filter fun (n, _) =>
      (n.toString == sourceName || (isPrivateName n && n.toString.endsWith ("." ++ sourceName))) &&
      ((env.getModuleIdxFor? n).any fun i => env.header.moduleNames[i.toNat]!.toString == owner)
    unless hits.length == 1 do throwError "root mismatch {owner}/{sourceName}: {hits.length}"
    let (root, _) := hits.head!
    let axs ← liftCoreM <| Lean.collectAxioms root
    logInfo m!"AX|{(Json.mkObj [("root", toJson sourceName), ("owner", toJson owner), ("kernel", toJson root.toString), ("axioms", toJson ((axs.qsort Name.lt).toList.map Name.toString))]).compress}"
  logInfo m!"COMPLETE|{roots.length}"
'''
for key,rs in [('Current',roots),('Baseline',[r for r in roots if r['name']!='Turing.MultiTapeTM.runFrom_one'])]:
    payload='['+', '.join('('+json.dumps(r['path'][:-5].replace('/','.'))+', '+json.dumps(r['name'])+')' for r in rs)+']'
    s=imports+ax.replace('ROOTS',payload)
    (O/('AX'+key+'.lean.txt')).write_text(s);(P/('AX'+key+'.lean')).write_text(s)
# Independent complete-owner API inventory: original imports, whole exact home
# source including the API, then a read-only environment traversal.
api=(W/'TCSlib/Complexity/TuringMachine/CfgFacts.lean').read_text()
api=api.replace('import TCSlib.Complexity.TuringMachine.StateRenaming\n','import TCSlib.Complexity.TuringMachine.StateRenaming\nimport Lean\n')
template_path=Path('/private/tmp/ab34-overnight-sg1-extras/prepare-inventories.py');s=template_path.read_text();template=s.split("template='''",1)[1].split("'''",1)[0]
src=api+template.replace('ROOTS','["Turing.MultiTapeTM.runFrom_one"]')
(O/'APIInventory.lean.txt').write_text(src);(P/'APIInventory.lean').write_text(src)
(O/'planned-probe-roots.json').write_text(json.dumps(roots,indent=2)+'\n')
print('Prepared AX current/baseline roots',len(roots),'and whole-owner API reachability inventory; no Lean started.')
