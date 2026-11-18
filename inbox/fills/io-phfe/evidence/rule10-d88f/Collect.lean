import Lean
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Efficient
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.PathAlgebra
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.PrefixAlgebra
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PolynomialTensorAlgebra
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Run
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.TwoStage
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearCorrect
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Endpoint
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Fresh
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Keys
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Reductions
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Slack
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Theorems
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Adapter
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.CommittedSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Core
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Correctness
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Embedding
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Encodings
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Headlines
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Simulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Widths
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticCorrect
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Advice
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Compose
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Derived
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Fresh
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Reduction
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Theorems
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Assembly
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Garbling
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.LinearEfficiency
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.MatrixDH
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Scheme
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Sim
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireDraws
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireLemmas
import TCSlib.Cryptography.Pairing.Exponents
import TCSlib.Cryptography.Pairing.Linear
import TCSlib.Cryptography.Pairing.MatrixDH
import TCSlib.Cryptography.Pairing.MatrixDH.AdaptiveShear
import TCSlib.Cryptography.Pairing.MatrixDH.ColumnLaws
import TCSlib.Cryptography.Pairing.MatrixDH.Defs
import TCSlib.Cryptography.Pairing.MatrixDH.Diagonal
import TCSlib.Cryptography.Pairing.MatrixDH.FiniteLinear
import TCSlib.Cryptography.Pairing.MatrixDH.Hardness
import TCSlib.Cryptography.Pairing.MatrixDH.Parameters
import TCSlib.Cryptography.Pairing.MatrixDH.SelfReduction

/-! nm-cca2 review collector (PkCollect with the five owners):
ROOT/CLOSURE for the five touched modules, CAT for every TCSlib definition in the environment. -/

set_option maxHeartbeats 0
set_option maxRecDepth 65536

open Lean Elab Command

def owners : List Name := [
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Efficient,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Simulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Layered,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.PathAlgebra,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.PrefixAlgebra,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PolynomialTensorAlgebra,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Run,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Security,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Simulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Security,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.TwoStage,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Linear,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearCorrect,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Endpoint,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Fresh,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Keys,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Reductions,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Slack,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Theorems,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Adapter,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.CommittedSimulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Core,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Correctness,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Embedding,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Encodings,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Headlines,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Raw,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Security,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Simulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Widths,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Quadratic,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticCorrect,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Advice,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Compose,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Data,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Derived,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Fresh,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Games,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Reduction,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Theorems,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSimulator,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Assembly,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Garbling,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.LinearEfficiency,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.MatrixDH,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Scheme,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Sim,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireDraws,
  `TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireLemmas,
  `TCSlib.Cryptography.Pairing.Exponents,
  `TCSlib.Cryptography.Pairing.Linear,
  `TCSlib.Cryptography.Pairing.MatrixDH,
  `TCSlib.Cryptography.Pairing.MatrixDH.AdaptiveShear,
  `TCSlib.Cryptography.Pairing.MatrixDH.ColumnLaws,
  `TCSlib.Cryptography.Pairing.MatrixDH.Defs,
  `TCSlib.Cryptography.Pairing.MatrixDH.Diagonal,
  `TCSlib.Cryptography.Pairing.MatrixDH.FiniteLinear,
  `TCSlib.Cryptography.Pairing.MatrixDH.Hardness,
  `TCSlib.Cryptography.Pairing.MatrixDH.Parameters,
  `TCSlib.Cryptography.Pairing.MatrixDH.SelfReduction]

def nameParts : Name → List (String × String)
  | .anonymous => []
  | .str p s => nameParts p ++ [("str", s)]
  | .num p n => nameParts p ++ [("num", toString n)]

def ident (n : Name) : Json := Json.mkObj [("display", toJson n.toString), ("components", toJson (nameParts n))]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames
  let idx : Std.HashMap Name Nat := names.size.fold (fun i _ m => m.insert names[i]! i) {}
  -- transitive TCSlib import closures
  for o in owners do
    let some i := idx[o]? | throwError "owner not loaded: {o}"
    let mut seen : Std.HashSet Name := {}
    let mut stack : Array Name := (env.header.moduleData[i]!.imports.map (·.module))
    while !stack.isEmpty do
      let m := stack.back!
      stack := stack.pop
      if seen.contains m then continue
      seen := seen.insert m
      if let some j := idx[m]? then
        stack := stack ++ env.header.moduleData[j]!.imports.map (·.module)
    let tcs := (seen.toArray.filter fun m => (`TCSlib).isPrefixOf m).qsort (·.toString < ·.toString)
    IO.println ("CLOSURE " ++ (Json.mkObj [("module", toJson o.toString), ("closure", toJson (tcs.map (·.toString)))]).compress)
  let mut catCount := 0
  let mut rootCount : Std.HashMap Name Nat := {}
  for (n, c) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := names[mi.toNat]!
    unless (`TCSlib).isPrefixOf home do continue
    if c.isDefinition then
      let abbrevFlag := match c with
        | .defnInfo d => match d.hints with | .abbrev => true | _ => false
        | _ => false
      IO.println ("CAT " ++ (Json.mkObj [("name", ident n), ("home", ident home), ("kind", toJson (kindOf c)),
        ("status", toJson (match Lean.getReducibilityStatusCore env n with
            | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible")),
        ("instance", toJson (Lean.Meta.isInstanceCore env n)), ("matcher", toJson (Lean.Meta.isMatcherCore env n)),
        ("abbrev", toJson abbrevFlag)]).compress)
      catCount := catCount + 1
    if owners.contains home then
      rootCount := rootCount.insert home ((rootCount[home]?.getD 0) + 1)
      let refs (e : Expr) : Array Json := Id.run do
        let mut out := #[]
        for d in e.getUsedConstants do
          let some dj := env.getModuleIdxFor? d | continue
          let dh := names[dj.toNat]!
          unless (`TCSlib).isPrefixOf dh && dh != home do continue
          let some di := env.find? d | continue
          unless di.isDefinition do continue
          out := out.push (ident d)
        return out
      let valueRefs := match c.value? (allowOpaque := true) with | some v => refs v | none => #[]
      IO.println ("ROOT " ++ (Json.mkObj [("module", toJson home.toString), ("name", ident n), ("kind", toJson (kindOf c)),
        ("type_refs", toJson (refs c.type)), ("value_refs", toJson valueRefs)]).compress)
  IO.println s!"CAT-COUNT {catCount}"
  for o in owners do
    IO.println s!"MODULE {o}: stored {rootCount[o]?.getD 0}"

run_cmd IO.println "PHFE_SNAPSHOT {\"head\": \"d88f0284cb898f940e9e2c6a5690233422a79e30\", \"snapshot_sha256\": \"627e8f129ea1a1691dfa2e8e264acd0a408c01a1570d81f63ae1820c8958d25a\"}"
