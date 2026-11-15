from pathlib import Path
import sys

phase = sys.argv[1]
folder = Path('evidence/axioms') / phase
folder.mkdir(parents=True, exist_ok=True)
source = r'''import Lean
import TCSlib.Cryptography.Randomness.Derandomization

set_option maxHeartbeats 0
set_option maxRecDepth 65536

run_cmd do
  let env ← Lean.getEnv
  let host := `Complexity.exists_seedMajorityTM
  let audit (root : Lean.Name) (blockHost : Bool) := Id.run do
    let mut todo : List (Lean.Name × List Lean.Name) := [(root, [root])]
    let mut seen : Lean.NameSet := {}
    let mut witness : Option (List Lean.Name) := none
    while !todo.isEmpty && witness.isNone do
      let (name, path) := todo.head!
      todo := todo.tail!
      if name == `sorryAx then
        witness := some path
      else if !(blockHost && name == host) && !seen.contains name then
        seen := seen.insert name
        if let some info := env.checked.get.find? name then
          for dependency in info.getUsedConstantsAsSet do
            todo := (dependency, path ++ [dependency]) :: todo
    return (seen.size, witness)
  for name in [host, `Complexity.seedMajority_mem_DTIME,
      `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp] do
    unless (env.checked.get.find? name).isSome do throwError "Missing target {name}"
    let (visited, path) := audit name false
    let (blockedVisited, blockedPath) := audit name true
    let row := Lean.Json.mkObj [
      ("target", Lean.toJson name.toString),
      ("visited", Lean.toJson visited),
      ("sorry_path", Lean.toJson (path.map (List.map Lean.Name.toString))),
      ("host_blocked_visited", Lean.toJson blockedVisited),
      ("host_blocked_sorry_path", Lean.toJson (blockedPath.map (List.map Lean.Name.toString)))]
    Lean.logInfo m!"DERAND-HOST-PATH {row.compress}"
    if blockedPath.isSome then
      throwError "A sorry dependency bypasses the host contract: {name}"
  Lean.logInfo "DERAND-HOST-PATHS PASS: removing the host eliminates every sorry path"
'''
(folder / 'HostPaths.lean').write_text(source)
(folder / 'host-paths-order.txt').write_text(str(folder / 'HostPaths') + '\n')
print(folder / 'HostPaths.lean')
