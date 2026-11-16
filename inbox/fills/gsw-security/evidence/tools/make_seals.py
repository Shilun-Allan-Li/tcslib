"""Prepare whole-file, full-import-closure Rule 10 seal probes (gsw-security).

Adapted from the derand fill's harness
(exchange `inbox/fills/derand/evidence/verification/tools/make_seals.py`, whose installation
and instance-unfolding mask follow Gate 10's archived harness); only the labels, the paths
and the command-line interface differ. Each probe is the source file with, after its last
`import`, `import Lean` and a `run_cmd` that enumerates every imported TCSlib definition
(actual `Lean.Name`s from the environment; no hand-picked list) and makes each eligible one
`local irreducible`, and erases it from the global-instance set so that instances are not
unfolded either. The file's own declarations come after the block and are never sealed.

Eligible: TCSlib-home definitions that are not reducible (matchers are included), minus
  * variant A: `Complexity.PolyExpr.eval` (notation, exempt); variant B seals it;
  * variant coe: instances whose body is `CoeFun.mk`/`Coe.mk` of a projection (projection
    coercions are notation, Seyoon 2026-11-14); variant strict seals them too.
The coe variant of seal A is canonical. Every eligible name, its home module and its flags
are logged (`GSWSEC-CATALOG`), then `GSWSEC-INSTALL` counts, then `GSWSEC-EOF` at the end.

Usage (python3 -I, from the fill checkout root):
    make_seals.py <phase> --file <path.lean> [--file ...] [--base <commit>] [--out <dir>]
Writes <out>/<phase>/<stem>_<A|B>_<strict|coe>.lean, a `.linemap.json` per probe (probe line ->
source line), `manifest.json` and `order.txt`. Default out: probes/seals.
"""
import argparse
import json
from pathlib import Path
import subprocess

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
    let instanceFlag := Lean.Meta.isInstanceCore env name
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
      !(projectionCoes && instanceFlag && coeProjection)
    let row := Lean.Json.mkObj [
      ("name", Lean.toJson name.toString), ("components", Lean.toJson (parts name)),
      ("home", Lean.toJson home.toString), ("home_components", Lean.toJson (parts home)),
      ("status", Lean.toJson status.toAttrString), ("matcher", Lean.toJson matcher),
      ("instance", Lean.toJson instanceFlag), ("projection_coercion", Lean.toJson coeProjection),
      ("eligible", Lean.toJson eligible)]
    Lean.logInfo m!"GSWSEC-CATALOG {label} {row.compress}"
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
    unless installed == .irreducible do throwError "GSWSEC seal installation failed: {name}"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do throwError "GSWSEC seal requires base scope"
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
    if scopedNames.contains name then throwError "GSWSEC scoped instance overlap: {name}"
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      requested.foldl (fun state name => state.erase name) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "GSWSEC typeclass lookup changed"
  for name in requested do
    if Lean.Meta.isGlobalInstance maskedEnv name then
      throwError "GSWSEC instance unfolding mask failed: {name}"
  Lean.logInfo m!"GSWSEC-INSTALL {label} requested={requested.size} active={active} already={already} excluded={excluded} tc_state=preserved"

'''

EOF = r'''

run_cmd do
  let label := "LABEL"
  Lean.logInfo m!"GSWSEC-EOF {label}"
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
    parser.add_argument('--base')
    parser.add_argument('--file', action='append', required=True)
    parser.add_argument('--out', default='probes/seals')
    args = parser.parse_args()
    out = Path(args.out) / args.phase
    out.mkdir(parents=True, exist_ok=True)
    manifest = []
    for path in args.file:
        if args.base:
            src = subprocess.check_output(['git', 'show', f'{args.base}:{path}'], text=True)
        else:
            src = Path(path).read_text()
        stem = path[:-5].replace('/', '_')
        for mode in ['A', 'B']:
            for coe in [False, True]:
                variant = f'{mode}_{"coe" if coe else "strict"}'
                label = f'{args.phase}_{stem}_{variant}'
                probe, mapping, offset = prepare(src, label, mode, coe)
                dest = out / f'{stem}_{variant}.lean'
                dest.write_text(probe)
                dest.with_suffix('.linemap.json').write_text(json.dumps(mapping) + '\n')
                manifest.append(dict(source=path, base=args.base, probe=str(dest), label=label,
                                     mode=mode, coe=coe, source_offset=offset))
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    (out / 'order.txt').write_text(''.join(r['probe'][:-5] + '\n' for r in manifest))
    print(f'Prepared {len(manifest)} seals under {out}')


if __name__ == '__main__':
    main()
