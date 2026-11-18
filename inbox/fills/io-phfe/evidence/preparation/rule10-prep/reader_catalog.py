#!/usr/bin/env python3
"""Generate a dormant native reader/projection census probe; never runs Lean or Git."""
import argparse, hashlib, json
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('snapshot',type=Path); ap.add_argument('out',type=Path); a=ap.parse_args()
c=json.loads((a.snapshot/'controls-coverage.json').read_text())
mods=(a.snapshot/'modules.txt').read_text().splitlines()
rows=[x for x in c['rows'] if x['requested_pair']]
entries=',\n'.join('    ('+json.dumps(x['name'])+', '+json.dumps(x['reader'] or '')+')' for x in rows)
source='import Lean\n'+''.join('import '+m+'\n' for m in mods)+'''
set_option maxHeartbeats 0
set_option maxRecDepth 65536
open Lean Elab Command

def phfeOwners : List Name := [
  '''+',\n  '.join('`'+m for m in mods)+''']

def phfeReaderPairs : Array (String × String) := #[
'''+entries+'''
]

run_cmd do
  let env ← getEnv
  let mut byString : Std.HashMap String (Array Name) := {}
  for (n, _) in env.constants.toList do
    byString := byString.insert n.toString (((byString[n.toString]?).getD #[]).push n)
  let mut verified := 0
  for (target, reader) in phfeReaderPairs do
    let targets := (byString[target]?).getD #[]
    let readers := (byString[reader]?).getD #[]
    if targets.size != 1 || readers.size != 1 then
      IO.println ("PHFE_READER " ++ (Json.mkObj [("target", toJson target),
        ("reader", toJson reader), ("ok", toJson false),
        ("reason", toJson "missing or ambiguous actual Lean name")]).compress)
      continue
    let t := targets[0]!
    let r := readers[0]!
    let some ci := env.find? r | throwError "reader vanished"
    let theoremFlag := match ci with | .thmInfo _ => true | _ => false
    let containsTarget := ci.type.getUsedConstants.contains t
    let ok := theoremFlag && containsTarget
    let home := (env.getModuleIdxFor? r).map fun i => env.header.moduleNames[i.toNat]!.toString
    IO.println ("PHFE_READER " ++ (Json.mkObj [("target", toJson target),
      ("reader", toJson reader), ("reader_home", toJson home), ("ok", toJson ok),
      ("reader_is_theorem", toJson theoremFlag),
      ("reader_type_mentions_target", toJson containsTarget)]).compress)
    if ok then verified := verified + 1
  for (n, ci) in env.constants.toList do
    let some i := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[i.toNat]!
    unless phfeOwners.contains home do continue
    unless ci.isDefinition do continue
    let proofFlag ← Lean.Elab.Command.liftTermElabM <| Lean.Meta.isProp ci.type
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    IO.println ("PHFE_DEFINITION " ++ (Json.mkObj [("name", toJson n.toString),
      ("home", toJson home.toString), ("projection", toJson (env.isProjectionFn n)),
      ("instance", toJson (Lean.Meta.isInstanceCore env n)),
      ("matcher", toJson (Lean.Meta.isMatcherCore env n)),
      ("abbrev", toJson abbrevFlag), ("proof_valued", toJson proofFlag)]).compress)
  IO.println ("PHFE_READER_DONE " ++ (Json.mkObj [("requested", toJson phfeReaderPairs.size),
    ("verified", toJson verified)]).compress)
  unless verified == phfeReaderPairs.size do
    throwError "PHFE reader census incomplete: {verified}/{phfeReaderPairs.size}"
'''
snap=json.loads((a.snapshot/'snapshot.json').read_text())
marker={'head':snap['head_at_snapshot'],
        'snapshot_sha256':hashlib.sha256((a.snapshot/'snapshot.json').read_bytes()).hexdigest()}
source+='\nrun_cmd IO.println '+json.dumps('PHFE_SNAPSHOT '+json.dumps(marker))+'\n'
a.out.parent.mkdir(parents=True,exist_ok=True); a.out.write_text(source)
print(json.dumps({'status':'PREPARED_NOT_RUN','requested_readers':len(rows),'verified':0,'out':str(a.out)}))
