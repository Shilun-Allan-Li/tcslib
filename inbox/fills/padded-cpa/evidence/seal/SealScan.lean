import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
open Lean Elab Command Meta

/-! Foreign-reference scan of the padded-cpa fill (adapted from the s2b-efficiency scan). Roots:
every declaration of the two helper modules `PublicKey.OracleSecurity.{ChallengeSim,
RecordHandler}`, and the touched declarations of `PublicKey.OracleSecurity` (the target and the
six private helpers). For each root, every constant of its type and value is collected, following
auxiliary declarations of the same module (matchers, `proof_`, `eq_`, internal names); a constant
is **foreign** when it is a TCSlib definition (`defnInfo`) of a module other than the root's. One
line per foreign definition: module, reducibility, projection or instance flag, the scanned modules
that use it. A second list reports every TCSlib instance (of any module) that the roots use. -/

def helperMods : Array Name := #[
  `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim,
  `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler]

def ownerMod : Name := `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

def touchedLast : List String := ["cpaAns", "polyTimeComputable_cpaAns", "cpaAns_seedIn",
  "ofFn_splitHalf_bit", "expect_simulate_indImpl_cpa", "padded_cpa_advantage_eq"]

def target : Name := `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  let mut roots : Array Name := #[target]
  for (c, _) in env.constants.toList do
    if let some m := modOf c then
      if helperMods.contains m && !c.isInternal then roots := roots.push c
      if m == ownerMod then
        if let .str _ s := c then
          if touchedLast.contains s && (c.toString.splitOn "_private").length > 1 then
            roots := roots.push c
  let mut seen : NameSet := {}
  let mut todo : Array (Name × Name) := roots.filterMap fun c => (modOf c).map (·, c)
  let mut foreign : Std.HashMap Name (Array Name) := {}
  let mut insts : Std.HashMap Name (Array Name) := {}
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
      if mu.toString.startsWith "TCSlib" && isInstanceCore env u then
        let ms := insts.getD u #[]
        insts := insts.insert u (if ms.contains rm then ms else ms.push rm)
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
  let short (m : Name) := m.toString.replace "TCSlib.Cryptography.Encryption.PublicKey." ""
  let mut rows : Array String := #[]
  for (u, ms) in foreign.toList do
    let st := getReducibilityStatusCore env u
    let tag := match st with
      | .reducible => "reducible" | .irreducible => "irreducible" | _ => "regular"
    let proj := (env.getProjectionFnInfo? u).isSome
    let inst := isInstanceCore env u
    let mu := (modOf u).getD .anonymous
    rows := rows.push s!"{u} | {mu} | {tag}{if proj then " projection" else ""}{if inst then " instance" else ""} | used by {(ms.map short).toList}"
  for r in rows.qsort (· < ·) do
    IO.println r
  for (u, ms) in insts.toList do
    IO.println s!"INSTANCE {u} | {(modOf u).getD .anonymous} | used by {(ms.map short).toList}"
  IO.println s!"roots: {roots.size}, scanned: {scanned}, foreign definitions: {rows.size}, TCSlib instances used: {insts.size}"
