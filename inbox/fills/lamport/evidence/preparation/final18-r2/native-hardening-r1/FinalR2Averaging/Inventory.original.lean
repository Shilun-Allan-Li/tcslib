import Lean
import LamportEvidence.Seals.FinalR2Averaging.Snapshot0

set_option maxHeartbeats 0
open Lean Meta Elab Command

run_cmd do
  let target : String := "TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging"
  let ownHome : String := "LamportEvidence.Seals.FinalR2Averaging.Snapshot0"
  let payload : String := "TCSlib.Cryptography.Games.OracleComp\nTCSlib.Cryptography.Games.Probability\nTCSlib.InformationTheory.FinDist"
  let homes := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← getEnv
  unless env.header.moduleNames.any (fun m => m.toString == ownHome) do
    throwError "LAMP-INVENTORY missing own snapshot {ownHome}"
  for home in homes do
    unless env.header.moduleNames.any (fun m => m.toString == home) do
      throwError "LAMP-INVENTORY missing closure module {home}"
  let mut rows : Array String := #[]
  let mut axs : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!.toString
    unless home == ownHome || homes.contains home do continue
    let status ← liftCoreM <| getReducibilityStatus n
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let instanceFlag := isInstanceCore env n
    rows := rows.push s!"LAMP-CATALOG\t{target}\t{n.toString}\t{home}\t{ci.isDefinition}\t{instanceFlag}\t{matcher}\t{repr status}"
    if home == ownHome then
      let aa ← liftCoreM <| collectAxioms n
      let aa := aa.qsort (fun a b => a.toString < b.toString)
      axs := axs.push s!"LAMP-AXIOMS\t{target}\t{n.toString}\t{aa.toList}"
  for row in rows.qsort (· < ·) do logInfo m!"{row}"
  for row in axs.qsort (· < ·) do logInfo m!"{row}"
  logInfo m!"LAMP-INVENTORY-END\t{target}\t{rows.size}\t{axs.size}\t{homes.length}"

