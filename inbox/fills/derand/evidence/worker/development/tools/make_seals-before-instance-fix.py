"""Prepare full-import-closure Rule 10 probes, retaining source and line maps.

The installation and instance-unfolding mask follow Gate 10's archived harness
(gates/10-efficiency/verification.zip, probe/EfficiencySealEfficiency.lean).
Each probe enumerates actual imported Lean Names; no printed-name re-resolution
or hand-picked candidate list is used. A excludes PolyExpr.eval; B seals it.
The coe variant also excludes exact projection-bodied Coe/CoeFun instances.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

BASE = '01de2d8baed9113e4a099e13c5d50c81e6dbc66f'
FILES = [
    'TCSlib/Complexity/ClassP/DTIME.lean',
    'TCSlib/Complexity/Randomized/Classes.lean',
    'TCSlib/Complexity/Randomized/Build/IterateFind.lean',
    'TCSlib/Complexity/Randomized/SeedMajority.lean',
    'TCSlib/Cryptography/Randomness/Derandomization.lean',
]

INSTALL = r'''
set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "LABEL"
  let includeEval := INCLUDEEVAL
  let projectionCoes := PROJECTIONCOES
  let rec parts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => parts p ++ [("str", s)]
    | .num p n => parts p ++ [("num", toString n)]
  let rec isProjectionBody (e : Lean.Expr) : Bool :=
    match e.consumeMData with
    | .lam _ _ body _ => isProjectionBody body
    | value => match value.getAppFn with
      | .const n _ => env.isProjectionFn n
      | _ => false
  let rec stripLambdas (e : Lean.Expr) : Lean.Expr :=
    match e.consumeMData with
    | .lam _ _ body _ => stripLambdas body
    | value => value
  let mut requested : Array Lean.Name := #[]
  let mut excluded : Nat := 0
  for (name, ci) in env.constants.toList.toArray.qsort (fun a b => Lean.Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let home := env.header.moduleNames[idx.toNat]!
    unless home.getRoot == `TCSlib && ci.isDefinition do continue
    let status := Lean.getReducibilityStatusCore env name
    let matcher := Lean.Meta.isMatcherCore env name
    let instance := Lean.Meta.isInstanceCore env name
    let coeProjection := match ci with
      | .defnInfo d =>
        let value := stripLambdas d.value
        match value.getAppFn with
        | .const n _ =>
          (n == `CoeFun.mk || n == `Coe.mk) &&
            value.getAppArgs.back?.any isProjectionBody
        | _ => false
      | _ => false
    let eligible := (status != .reducible || matcher) &&
      (includeEval || name != `Complexity.PolyExpr.eval) &&
      !(projectionCoes && instance && coeProjection)
    let row := Lean.Json.mkObj [
      ("name", Lean.toJson name.toString), ("components", Lean.toJson (parts name)),
      ("home", Lean.toJson home.toString), ("home_components", Lean.toJson (parts home)),
      ("status", Lean.toJson status.toAttrString), ("matcher", Lean.toJson matcher),
      ("instance", Lean.toJson instance), ("projection_coercion", Lean.toJson coeProjection),
      ("eligible", Lean.toJson eligible)]
    Lean.logInfo m!"DERAND-CATALOG {label} {row.compress}"
    if eligible then requested := requested.push name else excluded := excluded + 1
  let mut active : Nat := 0
  let mut already : Nat := 0
  for name in requested do
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    if before == .irreducible then already := already + 1
    else
      let id := Lean.mkIdent name
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    unless installed == .irreducible do throwError "DERAND seal installation failed: {name}"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do throwError "DERAND seal requires base scope"
  let mut scopedNames : Std.HashSet Lean.Name := {}
  for (_, payloads) in scopes.scopedEntries.map.toList do
    for name in payloads do scopedNames := scopedNames.insert name
  let entryFields (entry : Lean.Meta.InstanceEntry) :=
    (entry.keys, Lean.ExprStructEq.mk entry.val, entry.priority, entry.globalName?,
      entry.synthOrder, entry.attrKind)
  let lookupSnapshot (environment : Lean.Environment) :=
    let state := Lean.Meta.instanceExtension.getState environment
    (state.discrTree.toArray.map (fun (keys, entry) => (keys, entryFields entry)),
      state.instanceNames.toArray.map (fun (name, entry) => (name, entryFields entry)),
      state.erased.toList)
  let beforeLookup := lookupSnapshot env
  for name in requested do
    if scopedNames.contains name then throwError "DERAND scoped instance overlap: {name}"
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      requested.foldl (fun state name => state.erase name) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "DERAND typeclass lookup changed"
  for name in requested do
    if Lean.Meta.isGlobalInstance maskedEnv name then
      throwError "DERAND instance unfolding mask failed: {name}"
  Lean.logInfo m!"DERAND-INSTALL {label} requested={requested.size} active={active} already={already} excluded={excluded} tc_state=preserved"

'''

EOF = r'''

run_cmd do
  let label := "LABEL"
  Lean.logInfo m!"DERAND-EOF {label}"
'''

def prepare(src, label, mode, coe):
    lines = src.splitlines(keepends=True)
    last = max(i for i, line in enumerate(lines) if line.startswith('import '))
    block = INSTALL.replace('LABEL', label).replace('INCLUDEEVAL', str(mode == 'B').lower())
    block = block.replace('PROJECTIONCOES', str(coe).lower())
    head = ''.join(lines[:last + 1]) + 'import Lean\n' + block
    probe = head + ''.join(lines[last + 1:]) + EOF.replace('LABEL', label)
    offset = head.count('\n') - (last + 1)
    mapping = [None] * head.count('\n') + list(range(last + 2, len(lines) + 1))
    mapping += [None] * (probe.count('\n') - len(mapping))
    return probe, mapping, offset

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('phase')
    parser.add_argument('--base', action='store_true')
    parser.add_argument('--file', action='append', default=[])
    args = parser.parse_args()
    out = Path('evidence/seals') / args.phase
    out.mkdir(parents=True, exist_ok=True)
    manifest = []
    for path in args.file or FILES:
        if args.base:
            src = subprocess.check_output(['git', 'show', f'{BASE}:{path}'], text=True)
        else:
            src = Path(path).read_text()
        stem = path[:-5].replace('/', '_')
        for mode in ['A', 'B']:
            for coe in [False, True]:
                label = f'{args.phase}_{stem}_{mode}_{"coe" if coe else "strict"}'
                probe, mapping, offset = prepare(src, label, mode, coe)
                dest = out / f'{stem}_{mode}_{"coe" if coe else "strict"}.lean'
                dest.write_text(probe)
                dest.with_suffix('.linemap.json').write_text(json.dumps(mapping) + '\n')
                manifest.append(dict(source=path, probe=str(dest), label=label, mode=mode,
                                     coe=coe, source_offset=offset))
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    (out / 'order.txt').write_text(''.join(r['probe'][:-5] + '\n' for r in manifest))
    print(f'Prepared {len(manifest)} seals under {out}')

if __name__ == '__main__':
    main()
