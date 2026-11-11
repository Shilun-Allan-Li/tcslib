import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF

set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let owner := "TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF"
  for ref in #[`TCSlib.Cryptography.Composability.FixedLengthScheme.inLens,
      `TCSlib.Cryptography.Composability.FixedLengthScheme.outLens] do
    let some idx := env.getModuleIdxFor? ref | throwError "Missing interface dependency {ref}"
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus ref
    Lean.logInfo m!"CANDIDATE|{ref}|{env.header.moduleNames[idx.toNat]!}|{repr status}|instance=false|projection=false"
  for (name, ci) in env.constants.toList do
    let some midx := env.getModuleIdxFor? name | continue
    if env.header.moduleNames[midx.toNat]!.toString != owner then continue
    if (name.toString.splitOn "cca2").length < 2 then continue
    Lean.logInfo m!"DECL|{name}"
    let axioms ← Lean.collectAxioms name
    Lean.logInfo m!"AXIOMS|{name}|{axioms}"
    for ref in ci.getUsedConstantsAsSet.toList do
      let some idx := env.getModuleIdxFor? ref | continue
      let home := env.header.moduleNames[idx.toNat]!.toString
      if home == owner || !home.startsWith "TCSlib." then continue
      let some info := env.find? ref | continue
      let isInst := Lean.Meta.isInstanceCore env ref
      Lean.logInfo m!"FOREIGN|{name}|{ref}|{home}|definition={info.isDefinition}|instance={isInst}"
      if info.isDefinition then
        let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus ref
        Lean.logInfo m!"CANDIDATE|{ref}|{home}|{repr status}|instance={isInst}|projection={env.isProjectionFn ref}"
