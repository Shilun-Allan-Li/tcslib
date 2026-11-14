import Lean
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Hashing.FromDiscreteLog

/-! dl-crh exact-base closure collector -/

set_option maxHeartbeats 0
set_option maxRecDepth 65536

open Lean Elab Command

def owners : List Name := [
  `TCSlib.Cryptography.Candidates.DiscreteLog,
  `TCSlib.Cryptography.Hashing.FromDiscreteLog]

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
