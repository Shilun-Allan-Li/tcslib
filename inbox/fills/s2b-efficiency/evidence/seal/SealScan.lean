import TCSlib.Cryptography.Games.Efficiency
open Lean Elab Command Meta

/-! Foreign-reference scan of the efficiency fill. Roots: every declaration of the six helper
modules `TCSlib.Cryptography.Games.Efficiency.*` and the four targets of
`TCSlib.Cryptography.Games.Efficiency`. For each root, every constant of its type and value is
collected, following auxiliary declarations of the same module (matchers, `proof_`, `eq_`,
internal names); a constant is **foreign** when it is a TCSlib definition (`defnInfo`) of a module
other than the root's. One line per foreign definition: module, reducibility, projection or
instance flag, the scanned modules that use it. -/

def helperMods : Array Name := #[`TCSlib.Cryptography.Games.Efficiency.Strings,
  `TCSlib.Cryptography.Games.Efficiency.Replay, `TCSlib.Cryptography.Games.Efficiency.Handler,
  `TCSlib.Cryptography.Games.Efficiency.OracleBridge,
  `TCSlib.Cryptography.Games.Efficiency.Interactive,
  `TCSlib.Cryptography.Games.Efficiency.InteractiveSpec]

def targets : Array Name := #[`TCSlib.Cryptography.Games.exists_handlerMachine,
  `TCSlib.Cryptography.Games.exists_interactiveHandlerMachine,
  `TCSlib.Cryptography.Games.exists_toCompOn_of_toComp,
  `TCSlib.Cryptography.Games.exists_toOracleAdversary_of_bitCodec]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  let mut roots : Array Name := targets
  for (c, _) in env.constants.toList do
    if let some m := modOf c then
      if helperMods.contains m && !c.isInternal then roots := roots.push c
  -- (root module, constant) work list
  let mut seen : NameSet := {}
  let mut todo : Array (Name × Name) := roots.filterMap fun c => (modOf c).map (·, c)
  let mut foreign : Std.HashMap Name (Array Name) := {}
  let mut scanned := 0
  while !todo.isEmpty do
    let (rm, c) := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    scanned := scanned + 1
    let some ci := env.find? c | continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    for u in used do
      let some mu := modOf u | continue
      if mu == rm then
        let s := u.toString
        if !seen.contains u && (u.isInternal || (s.splitOn "match_").length > 1 ||
            (s.splitOn "proof_").length > 1 || (s.splitOn "._unary").length > 1 ||
            (s.splitOn ".eq_").length > 1 || (s.splitOn "_sunfold").length > 1) then
          todo := todo.push (rm, u)
      else if mu.toString.startsWith "TCSlib" then
        if let some ui := env.find? u then
          if ui matches .defnInfo _ then
            let ms := foreign.getD u #[]
            foreign := foreign.insert u (if ms.contains rm then ms else ms.push rm)
  let mut rows : Array String := #[]
  for (u, ms) in foreign.toList do
    let st := getReducibilityStatusCore env u
    let tag := match st with
      | .reducible => "reducible" | .irreducible => "irreducible" | _ => "regular"
    let proj := (env.getProjectionFnInfo? u).isSome
    let inst := isInstanceCore env u
    let mu := (modOf u).getD .anonymous
    let users := ms.map fun m => m.toString.replace "TCSlib.Cryptography.Games." ""
    rows := rows.push s!"{u} | {mu} | {tag}{if proj then " projection" else ""}{if inst then " instance" else ""} | used by {users.toList}"
  for r in rows.qsort (· < ·) do
    IO.println r
  IO.println s!"roots: {roots.size}, scanned: {scanned}, foreign definitions: {rows.size}"
