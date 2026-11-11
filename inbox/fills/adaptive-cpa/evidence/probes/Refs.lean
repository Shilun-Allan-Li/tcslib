import Lean
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA

set_option maxHeartbeats 0

/-! Census of the foreign TCSlib references of the touched declarations (types and values,
including generated auxiliary declarations: matchers, equation and `simps` lemmas, proof
auxiliaries), for the adaptive-cpa seal. Touched: every declaration of the four new helper
modules, and the target with its auxiliaries in the owned module. -/
run_cmd do
  let env ← Lean.getEnv
  let base := "TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA"
  let helpers : List String := [base ++ ".Hybrid", base ++ ".Handler", base ++ ".Games",
    base ++ ".Reduction"]
  let target := "TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa"
  for (name, ci) in env.constants.toList do
    let some midx := env.getModuleIdxFor? name | continue
    let own := env.header.moduleNames[midx.toNat]!.toString
    let s := name.toString
    let touched := helpers.contains own || (own == base && (s == target || s.startsWith (target ++ ".")))
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
