import Lean
import TCSlib.Cryptography.Games.Forwarding
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

/- G06-HARNESS INSTALL ControlSingletonAS_inArg_part1 -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "ControlSingletonAS_inArg_part1"
  let payload : String := "Complexity.NUPPT.inArg\tTCSlib.Complexity.Randomized.Closure"
  let expectedRequests : Nat := 1
  let mut requests : Array (String × String) := #[]
  let payloadLines := if payload.isEmpty then [] else payload.splitOn "\n"
  for line in payloadLines do
    match line.splitOn "\t" with
    | [spelling, home] =>
      unless !spelling.isEmpty && !home.isEmpty do throwError "G06-HARNESS {label}: empty request field"
      requests := requests.push (spelling, home)
    | _ => throwError "G06-HARNESS {label}: malformed serialized request row"
  unless requests.size == expectedRequests do throwError "G06-HARNESS {label}: serialized request count differs: {requests.size} vs {expectedRequests}"
  let rec nameParts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => nameParts p ++ [("str", s)]
    | .num p n => nameParts p ++ [("num", toString n)]
  let nameKey (n : Lean.Name) : String := (Lean.toJson (nameParts n)).compress
  let componentPayload : String := "Complexity.NUPPT.inArg\t[[\"str\",\"Complexity\"],[\"str\",\"NUPPT\"],[\"str\",\"inArg\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"Randomized\"],[\"str\",\"Closure\"]]\tfalse\tfalse\tfalse"
  let mut components : Std.HashMap String (String × String × String × String × String) := {}
  for line in (if componentPayload.isEmpty then [] else componentPayload.splitOn "\n") do
    match line.splitOn "\t" with
    | [n, nk, hk, i, m, a] =>
      if (components[n]?).isSome then throwError "G06-HARNESS {label}: duplicate component request"
      components := components.insert n (nk, hk, i, m, a)
    | _ => throwError "G06-HARNESS {label}: malformed component request"
  unless components.size == requests.size do throwError "G06-HARNESS {label}: component count differs"
  let env ← Lean.getEnv
  let mut resolved : Array Lean.Name := #[]
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut verified : Nat := 0
  let mut active : Nat := 0
  let mut already : Nat := 0
  for (n, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for (spelling, expectedHome) in requests do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "G06-HARNESS {label}: absent/ambiguous imported name {spelling}; candidates={ns.size}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "G06-HARNESS {label}: no home for {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "G06-HARNESS {label}: home differs for {spelling}: {home}"
    let some ci := env.find? n | throwError "G06-HARNESS {label}: no constant for {spelling}"
    unless ci.isDefinition do throwError "G06-HARNESS {label}: requested nondefinition {spelling}"
    let some (nk, hk, ei, em, ea) := components[spelling]?
      | throwError "G06-HARNESS {label}: missing component request"
    unless nameKey n == nk && nameKey home == hk do
      throwError "G06-HARNESS {label}: actual Name components differ"
    let instanceFlag := Lean.Meta.isInstanceCore env n
    let matcherFlag := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    unless toString instanceFlag == ei && toString matcherFlag == em && toString abbrevFlag == ea do
      throwError "G06-HARNESS {label}: definition/instance metadata differs"
    Lean.logInfo m!"G06-COMPONENT label={label} phase=install spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}"
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if before == .irreducible then
      already := already + 1
    else
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed for {spelling}"
    resolved := resolved.push n
    verified := verified + 1
    Lean.logInfo m!"G06-NAME label={label} spelling={spelling} actual={n.toString} home={home} before={repr before} installed={repr installed}"
  unless active + already == requests.size do throwError "G06-HARNESS {label}: installation count mismatch"
  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do
    throwError "G06-HARNESS {label}: unfolding mask requires base scope"
  let mut scopedNames : Std.HashSet Lean.Name := {}
  for (_, payloads) in scopes.scopedEntries.map.toList do
    for n in payloads do
      scopedNames := scopedNames.insert n
  let mut removed : Nat := 0
  for n in resolved do
    if scopedNames.contains n then
      throwError "G06-HARNESS {label}: scoped unfolding payload intersects request {n}"
    if Lean.Meta.isGlobalInstance maskEnv n then
      removed := removed + 1
  -- InstanceEntry's BEq checks only val, so compare every field explicitly.
  let entryFields (e : Lean.Meta.InstanceEntry) :=
    (e.keys, Lean.ExprStructEq.mk e.val, e.priority, e.globalName?, e.synthOrder, e.attrKind)
  let lookupSnapshot (e : Lean.Environment) :=
    let s := Lean.Meta.instanceExtension.getState e
    (s.discrTree.toArray.map (fun (ks, entry) => (ks, entryFields entry)),
      s.instanceNames.toArray.map (fun (n, entry) => (n, entryFields entry)), s.erased.toList)
  let beforeLookup := lookupSnapshot env
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      resolved.foldl (fun s n => s.erase n) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "G06-HARNESS {label}: typeclass lookup state changed"
  for n in resolved do
    if Lean.Meta.isGlobalInstance maskedEnv n then
      throwError "G06-HARNESS {label}: unfolding membership after mask for {n}"
  Lean.logInfo m!"G06-MASK label={label} phase=install requested={requests.size} verified={resolved.size} removed={removed} scope_depth=1 scoped_names={scopedNames.size} tc_state=preserved"
  Lean.logInfo m!"G06-SEAL label={label} requested={requests.size} active={active} already_irreducible={already} verified={verified}"

namespace HashSignSensitivity

theorem negative (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := rfl

theorem positive (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := Complexity.NUPPT.inArg_eq z

end HashSignSensitivity

/- G06-HARNESS EOF-VERIFY ControlSingletonAS_inArg_part1 -/
set_option maxHeartbeats 0
run_cmd do
  let label : String := "ControlSingletonAS_inArg_part1"
  let payload : String := "Complexity.NUPPT.inArg\tTCSlib.Complexity.Randomized.Closure"
  let expectedRequests : Nat := 1
  let mut requests : Array (String × String) := #[]
  let payloadLines := if payload.isEmpty then [] else payload.splitOn "\n"
  for line in payloadLines do
    match line.splitOn "\t" with
    | [spelling, home] =>
      unless !spelling.isEmpty && !home.isEmpty do throwError "G06-HARNESS {label}: empty request field"
      requests := requests.push (spelling, home)
    | _ => throwError "G06-HARNESS {label}: malformed serialized request row"
  unless requests.size == expectedRequests do throwError "G06-HARNESS {label}: serialized request count differs: {requests.size} vs {expectedRequests}"
  let rec nameParts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => nameParts p ++ [("str", s)]
    | .num p n => nameParts p ++ [("num", toString n)]
  let nameKey (n : Lean.Name) : String := (Lean.toJson (nameParts n)).compress
  let componentPayload : String := "Complexity.NUPPT.inArg\t[[\"str\",\"Complexity\"],[\"str\",\"NUPPT\"],[\"str\",\"inArg\"]]\t[[\"str\",\"TCSlib\"],[\"str\",\"Complexity\"],[\"str\",\"Randomized\"],[\"str\",\"Closure\"]]\tfalse\tfalse\tfalse"
  let mut components : Std.HashMap String (String × String × String × String × String) := {}
  for line in (if componentPayload.isEmpty then [] else componentPayload.splitOn "\n") do
    match line.splitOn "\t" with
    | [n, nk, hk, i, m, a] =>
      if (components[n]?).isSome then throwError "G06-HARNESS {label}: duplicate component request"
      components := components.insert n (nk, hk, i, m, a)
    | _ => throwError "G06-HARNESS {label}: malformed component request"
  unless components.size == requests.size do throwError "G06-HARNESS {label}: component count differs"
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut verified : Nat := 0
  for (n, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for (spelling, expectedHome) in requests do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "G06-HARNESS {label}: absent/ambiguous imported name {spelling}; candidates={ns.size}"
    let n := ns[0]!
    let some mi := env.getModuleIdxFor? n | throwError "G06-HARNESS {label}: no home for {spelling}"
    let home := env.header.moduleNames[mi.toNat]!
    unless home.toString == expectedHome do throwError "G06-HARNESS {label}: home differs for {spelling}: {home}"
    let some ci := env.find? n | throwError "G06-HARNESS {label}: no constant for {spelling}"
    unless ci.isDefinition do throwError "G06-HARNESS {label}: requested nondefinition {spelling}"
    let some (nk, hk, ei, em, ea) := components[spelling]?
      | throwError "G06-HARNESS {label}: missing component request"
    unless nameKey n == nk && nameKey home == hk do
      throwError "G06-HARNESS {label}: actual Name components differ"
    let instanceFlag := Lean.Meta.isInstanceCore env n
    let matcherFlag := (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    unless toString instanceFlag == ei && toString matcherFlag == em && toString abbrevFlag == ea do
      throwError "G06-HARNESS {label}: definition/instance metadata differs"
    Lean.logInfo m!"G06-COMPONENT label={label} phase=eof spelling={spelling} key={nk} home_key={hk} instance={instanceFlag}"
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless installed == .irreducible do throwError "G06-HARNESS {label}: seal not installed at EOF for {spelling}"
    if Lean.Meta.isGlobalInstance env n then
      throwError "G06-HARNESS {label}: unfolding membership at EOF for {spelling}"
    verified := verified + 1
  unless verified == requests.size do throwError "G06-HARNESS {label}: verification count mismatch"
  Lean.logInfo m!"G06-MASK label={label} phase=eof requested={requests.size} verified={verified}"
  Lean.logInfo m!"G06-SEAL-END label={label} requested={requests.size} verified={verified}"

