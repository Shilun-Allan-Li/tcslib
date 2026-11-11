import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF

set_option maxHeartbeats 0

/-! Census of foreign TCSlib references of the touched declarations (types and values,
including generated auxiliary declarations), for the r2 seal. -/
run_cmd do
  let env ← Lean.getEnv
  let ns := "TCSlib.Cryptography.Composability.FixedLengthScheme."
  let readers : List String := [ns ++ "indSpec_decDom", ns ++ "indSpec_decRng",
    ns ++ "indSpec_challengeDom", ns ++ "indSpec_challengeRng", ns ++ "indImpl_dec_onSpec",
    ns ++ "indImpl_challenge_none_onSpec", "TCSlib.Cryptography.prfScheme_dec"]
  let ofp := "TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF"
  for (name, ci) in env.constants.toList do
    let some midx := env.getModuleIdxFor? name | continue
    let own := env.header.moduleNames[midx.toNat]!.toString
    let s := name.toString
    let touched := readers.any (fun r => s == r || s.startsWith (r ++ ".")) ||
      (own == ofp && (s.splitOn "cca2").length ≥ 2)
    unless touched do continue
    Lean.logInfo m!"DECL|{own}|{name}"
    for ref in ci.getUsedConstantsAsSet.toList do
      let some idx := env.getModuleIdxFor? ref | continue
      let home := env.header.moduleNames[idx.toNat]!.toString
      if home == own || !home.startsWith "TCSlib." then continue
      let some info := env.find? ref | continue
      let isInst := Lean.Meta.isInstanceCore env ref
      Lean.logInfo m!"FOREIGN|{own}|{name}|{ref}|{home}|definition={info.isDefinition}|instance={isInst}"
      if info.isDefinition then
        let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus ref
        Lean.logInfo m!"CANDIDATE|{own}|{ref}|{home}|{repr status}|instance={isInst}|projection={env.isProjectionFn ref}"
