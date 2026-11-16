#!/usr/bin/env python3
"""Prepare whole-file A/B, strict/coe seals without running Lean.
Adapted from sc-garble evidence/tools/make_seals.py, exchange a73072f1.
Only the issue base and output evidence directory differ.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('phase', choices=['base', 'final'])
parser.add_argument('files', nargs='+')
args = parser.parse_args()
base = '6ce4658db08a1dc2a03a149987197660db078011'
root = Path('evidence/subagents/b7/seals') / args.phase
root.mkdir(parents=True, exist_ok=True)
preamble = '''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && EVAL_NOTATION) ||
            (COE_NOTATION && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\\t{home}\\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\\t{home}\\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"
'''
manifest = []
for file in args.files:
    path = Path(file)
    try:
        source = (subprocess.check_output(['git', 'show', base + ':' + file],
                  stderr=subprocess.DEVNULL).decode() if args.phase == 'base'
                  else path.read_text())
    except subprocess.CalledProcessError:
        manifest.append(dict(file=file, status='ABSENT_AT_BASE'))
        continue
    imports = list(re.finditer(r'^import [^\n]+\n', source, re.M))
    assert imports, file
    insert = imports[-1].end()
    for variant in ['A', 'B']:
        for coe in ['strict', 'coe']:
            label = path.stem + '_' + variant + '_' + coe
            seal = preamble.replace('EVAL_NOTATION', str(variant == 'A').lower())
            seal = seal.replace('COE_NOTATION', str(coe == 'coe').lower())
            instrumented = source[:insert] + 'import Lean\n' + seal + source[insert:]
            output = root / (label + '.lean')
            output.write_text(instrumented)
            manifest.append(dict(file=file, probe=str(output), variant=variant,
                                 coercions=coe, original_insert_line=source[:insert].count('\n'),
                                 inserted_lines=('import Lean\n'+seal).count('\n')))
(root / 'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
(root / 'order.txt').write_text(''.join(x['probe'][:-5]+'\n' for x in manifest if 'probe' in x))
print('Prepared', sum('probe' in x for x in manifest), 'seals at', root)
