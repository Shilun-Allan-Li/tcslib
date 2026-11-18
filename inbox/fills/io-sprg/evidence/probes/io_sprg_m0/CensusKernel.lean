import Lean
import TCSlib.Cryptography.Obfuscation

set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option pp.explicit true
set_option pp.universes true
set_option pp.fullNames true

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
  let mut roots : Array Name := #[]
  for (n, c) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!
    unless owners.contains home do continue
    roots := roots.push n
    let row := Json.mkObj [("name", toJson n.toString), ("module", toJson home.toString),
      ("kind", toJson (kindOf c)), ("private", toJson (Lean.isPrivateName n)),
      ("internal", toJson n.isInternal)]
    IO.println ("ROOTMETA " ++ row.compress)
    unless Lean.isPrivateName n || n.isInternal do
      let ty := reprStr c.type
      IO.println ("STMT " ++ (Json.mkObj [("name", toJson n.toString),
        ("kind", toJson (kindOf c)), ("module", toJson home.toString),
        ("type", toJson ty)]).compress)
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.checked.get.find? n | continue
    let mut refs := #[]
    let mut isAxiom := false
    match c with
    | .axiomInfo v =>
        isAxiom := true
        refs := v.type.getUsedConstants
    | .defnInfo v => refs := v.type.getUsedConstants ++ v.value.getUsedConstants
    | .thmInfo v => refs := v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => refs := v.type.getUsedConstants ++ v.value.getUsedConstants
    | .ctorInfo v => refs := v.type.getUsedConstants
    | .recInfo v => refs := v.type.getUsedConstants
    | .inductInfo v => refs := v.type.getUsedConstants ++ v.ctors.toArray
    | .quotInfo _ => pure ()
    IO.println ("GRAPH " ++ (Json.mkObj [("name", toJson n.toString),
      ("axiom", toJson isAxiom), ("refs", toJson (refs.map Name.toString))]).compress)
    stack := stack ++ refs
  IO.println s!"GRAPH-COUNT {seen.size} ROOT-COUNT {roots.size}"
