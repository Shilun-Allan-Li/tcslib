import TCSlib.Cryptography.Candidates.ElGamal
open Lean Meta Elab Command

def dlcTargets : List String := ["statClose_sq_generator", "polyTimeComputable_egGenRaw",
  "polyTimeComputable_egEncRaw", "egDecStr_apply", "elGamal_correct",
  "polyTimeComputable_egGroupGenRaw", "elGamal_secure"]

elab "#dlc_foreign" : command => do
  let env ← getEnv
  let mine := `TCSlib.Cryptography.Candidates.ElGamal
  let some myIdx := env.getModuleIdx? mine | throwError "no module"
  let names := env.header.moduleData[myIdx.toNat]!.constNames
  let simpThms ← liftTermElabM getSimpTheorems
  let mut scanned : Array Name := #[]
  let mut found : NameSet := {}
  for n in names do
    let s := n.toString
    let isMine := (s.splitOn "dlc_").length > 1 ||
      dlcTargets.any (fun t => (s.splitOn ("Candidates." ++ t)).length > 1)
    if !isMine then continue
    scanned := scanned.push n
    let some ci := env.find? n | continue
    let mut cs := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
    for c in cs do
      let some cmod := env.getModuleIdxFor? c | continue
      let modName := env.header.moduleNames[cmod.toNat]!
      if modName == mine then continue
      if !(modName.toString.startsWith "TCSlib.") then continue
      let some cci := env.find? c | continue
      match cci with
      | .defnInfo _ =>
        if (← liftTermElabM (isProjectionFn c)) then continue
        found := found.insert c
      | _ => pure ()
  logInfo m!"scanned {scanned.size} declarations"
  for c in found.toList do
    let isSimp := simpThms.isDeclToUnfold c || simpThms.isLemma (.decl c)
    let isInst := isInstanceCore env c
    let modName := env.header.moduleNames[(env.getModuleIdxFor? c).get!.toNat]!
    let red ← getReducibilityStatus c
    logInfo m!"FOREIGN {c} simp={isSimp} inst={isInst} red={repr red} module={modName}"

#dlc_foreign
