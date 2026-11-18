import Lean
import TCSlib.Cryptography.Obfuscation

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option pp.all true

open Lean Elab Command

def owners : List Name := [
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.LPN,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.PolyTerms,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Degree,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Params,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Encoding,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.SparseFactor,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Polys,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Samplers,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Correctness,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Stretch,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Load,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Security,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets,
  `TCSlib.Cryptography.Obfuscation.StructuredSeed,
  `TCSlib.Cryptography.Obfuscation]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

run_cmd do
  let env ← getEnv
  let mut stored := 0
  let mut publicCount := 0
  let constants := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (n, c) in constants do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!
    unless owners.contains home do continue
    stored := stored + 1
    let axioms ← Lean.collectAxioms n
    let directRefs := match c.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    let row := Json.mkObj [("name", toJson n.toString), ("module", toJson home.toString),
      ("kind", toJson (kindOf c)), ("private", toJson (Lean.isPrivateName n)),
      ("internal", toJson n.isInternal), ("axioms", toJson (axioms.map Name.toString)),
      ("direct_sorryAx", toJson (directRefs.contains ``sorryAx))]
    IO.println ("CENSUS " ++ row.compress)
    unless Lean.isPrivateName n || n.isInternal do
      publicCount := publicCount + 1
      let type ← liftTermElabM fun _ => do
        let fmt ← Lean.Meta.ppExpr c.type
        pure fmt.pretty
      IO.println ("STMT " ++ (Json.mkObj [("name", toJson n.toString),
        ("kind", toJson (kindOf c)), ("module", toJson home.toString),
        ("type", toJson type)]).compress)
  IO.println s!"CENSUS-COUNT {stored} PUBLIC-COUNT {publicCount}"
