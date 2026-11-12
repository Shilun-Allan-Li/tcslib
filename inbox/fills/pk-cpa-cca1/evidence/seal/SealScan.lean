import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command Meta

/-! Foreign-reference scan of the pk-cpa-cca1 fill (as in the padded-cpa and bitwise-cpa fills).
Roots: every declaration of the six helper modules `PrivateKey.OracleFromPRF.{Games, Handler,
Reduction, Transfer, Lazy, Collision}`, the touched declarations of `PrivateKey.OracleFromPRF` (the
two targets and the fourteen private declarations of section `PRFStep`), and the four authorized
readers of `PrivateKey.OracleSecurity`. For each root, every constant of its type and value is
collected, following auxiliary declarations of the same module (matchers, `proof_`, `eq_`,
internal names); a constant is **foreign** when it is a TCSlib definition (`defnInfo`) of a module
other than the root's (so a helper module's definitions are foreign to the other helpers). One line
per foreign definition: module, reducibility, projection or instance flag, the scanned modules that
use it. A second list reports every TCSlib instance (of any module) that the roots use. -/

def helperMods : Array Name := #[
  `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games,
  `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler,
  `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction,
  `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer,
  `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy,
  `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision]

def ownerMod : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF

def touchedPrivate : List String := ["prf_gen_runAt", "prfKeyEq", "ofFn_prfKeyEq", "prfNonceEq",
  "ofFn_prfNonceEq", "ofFn_prf_encryptAt", "ofFn_prf_decAnswer", "prf_ctLen_eval", "prf_inLens",
  "prf_outLens", "accept_prf_indGame", "prfAdv_prfReduction", "prf_advantage_le", "prf_indSecure"]

def publicRoots : Array Name := #[
  `TCSlib.Cryptography.Composability.prfFixedScheme_cpa,
  `TCSlib.Cryptography.Composability.prfFixedScheme_cca1,
  `TCSlib.Cryptography.Composability.FixedLengthScheme.indSpec_encDom,
  `TCSlib.Cryptography.Composability.FixedLengthScheme.indSpec_encRng,
  `TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl_enc_onSpec,
  `TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl_challenge_repeat_onSpec]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Option Name :=
    (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!
  let mut roots : Array Name := publicRoots
  for (c, _) in env.constants.toList do
    if let some m := modOf c then
      if helperMods.contains m && !c.isInternal then roots := roots.push c
      if m == ownerMod then
        if let .str _ s := c then
          if touchedPrivate.contains s && (c.toString.splitOn "_private").length > 1 then
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
  let short (m : Name) := m.toString.replace "TCSlib.Cryptography.Encryption.PrivateKey." ""
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
