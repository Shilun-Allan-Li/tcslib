import Lean
import evidence.rule10.base.probes.BaseExtraction

set_option maxHeartbeats 0
open Lean Meta Elab Command

run_cmd do
  let owners : List String := ["evidence.rule10.base.probes.BaseExtraction"]
  let env ← getEnv
  let mut seen : Nat := 0
  let mut owned : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf home || owners.contains home.toString do continue
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "def"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let abbrev := match ci with
      | .defnInfo d => match d.hints with
        | .abbrev => true
        | _ => false
      | _ => false
    let mut status : String := "not_definition"
    if ci.isDefinition then
      let s ← liftCoreM <| getReducibilityStatus n
      status := reprStr s
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let row := Json.mkObj [
      ("record", toJson ("constant" : String)),
      ("name", toJson n.toString), ("home", toJson home.toString),
      ("kind", toJson kind), ("abbrev", toJson abbrev),
      ("status", toJson status), ("matcher", toJson matcher)]
    logInfo m!"FILL_CENSUS {row.compress}"
    seen := seen + 1
    if owners.contains home.toString then
      let axs ← liftCoreM <| collectAxioms n
      let names := (axs.qsort (fun a b => a.toString < b.toString)).toList.map (·.toString)
      let row := Json.mkObj [
        ("record", toJson ("axioms" : String)),
        ("name", toJson n.toString), ("home", toJson home.toString),
        ("axioms", toJson names)]
      logInfo m!"FILL_CENSUS {row.compress}"
      owned := owned + 1
  let summary := Json.mkObj [
    ("record", toJson ("complete" : String)),
    ("constants", toJson seen), ("owned", toJson owned),
    ("owners", toJson owners)]
  logInfo m!"FILL_CENSUS {summary.compress}"
