import Lean
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability

/-! nm-cca2 review collector (PkCollect with the five owners):
ROOT/CLOSURE for the five touched modules, CAT for every TCSlib definition in the environment. -/

/- dw10-seal-inventory (Claude lead, 2026-11-17): ADAPTED from the bb1-sim-statements NmCollect.template.lean (the
nm-cca2 review collector). The CLOSURE and CAT records and the existing ROOT fields are unchanged. Added:
(1) COEINST records: every TCSlib instance whose class is a coercion class (Coe, CoeTail, CoeHead, CoeOut, CoeTC, CoeOTC,
    CoeHTC, CoeHTCT, CoeDep, CoeFun, CoeSort, FunLike, DFunLike), with its class, home and reducibility (brief, suite item 1);
(2) ROOT fields for the owner check and the controls: `own_type_refs` (definitions of the owner's own module in the type),
    `flags` (private, internal user name, aux recursor, noConfusion, projection, instance, matcher, abbrev, reducibility);
(3) ROOT field `eqn_refs` (suite item 5, #248 channel C3): every constant used in the value whose user name ends in
    `eq_<n>`, `eq_def`, `eq_unfold` or `splitter`, with the target (the name without that suffix, resolved also through
    private names) when the target is a TCSlib definition of another module: ref, target, target home, target kind.
The owner list and the imports are replaced by mkcollect.py per batch. -/

set_option maxHeartbeats 0
set_option maxRecDepth 65536

open Lean Elab Command

def owners : List Name := [
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Readers,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability]

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
  -- dw10: user-name map of TCSlib constants (private names resolved), for eqn_refs targets
  let mut userMap : Std.HashMap Name Name := {}
  for (n, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf names[mi.toNat]! do continue
    let u := (privateToUserName? n).getD n
    unless userMap.contains u do userMap := userMap.insert u n
  let coeClasses : List Name := [``Coe, ``CoeTail, ``CoeHead, ``CoeOut, ``CoeTC, ``CoeOTC, ``CoeHTC, ``CoeHTCT,
    ``CoeDep, ``CoeFun, ``CoeSort, `FunLike, `DFunLike]
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
      if Lean.Meta.isInstanceCore env n then
        if let some cls := c.type.getForallBody.getAppFn.constName? then
          if coeClasses.contains cls then
            IO.println ("COEINST " ++ (Json.mkObj [("name", ident n), ("home", ident home), ("class", toJson cls.toString),
              ("status", toJson (match Lean.getReducibilityStatusCore env n with
                | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"))]).compress)
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
      -- dw10 additions
      let ownTypeRefs : Array Json := Id.run do
        let mut out := #[]
        for d in c.type.getUsedConstants do
          let some dj := env.getModuleIdxFor? d | continue
          unless names[dj.toNat]! == home && d != n do continue
          let some di := env.find? d | continue
          unless di.isDefinition do continue
          out := out.push (ident d)
        return out
      let eqnRefs : Array Json := Id.run do
        let mut out := #[]
        let used := (match c.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[]) ++ c.type.getUsedConstants
        for d in used do
          let u := (privateToUserName? d).getD d
          let isEqn := match u with
            | .str _ s => s == "eq_def" || s == "eq_unfold" || s == "splitter" ||
                (s.startsWith "eq_" && (s.drop 3).all Char.isDigit && (s.drop 3).length > 0)
            | _ => false
          unless isEqn do continue
          let t := u.getPrefix
          let tn := (if (env.find? t).isSome then some t else userMap[t]?)
          let some tn := tn | continue
          let some tj := env.getModuleIdxFor? tn | continue
          let th := names[tj.toNat]!
          unless (`TCSlib).isPrefixOf th && th != home do continue
          let some ti := env.find? tn | continue
          out := out.push (Json.mkObj [("ref", ident d), ("target", ident tn), ("target_home", toJson th.toString),
            ("target_kind", toJson (kindOf ti)), ("in", toJson (if (c.type.getUsedConstants.contains d) then "type" else "value"))])
        return out
      let flags := Json.mkObj [("private", toJson (isPrivateName n)), ("internal", toJson ((privateToUserName? n).getD n).isInternal),
        ("aux_recursor", toJson (isAuxRecursor env n)), ("no_confusion", toJson (isNoConfusion env n)),
        ("projection", toJson (env.isProjectionFn n)), ("instance", toJson (Lean.Meta.isInstanceCore env n)),
        ("matcher", toJson (Lean.Meta.isMatcherCore env n)),
        ("abbrev", toJson (match c with | .defnInfo d => (match d.hints with | .abbrev => true | _ => false) | _ => false)),
        ("status", toJson (match Lean.getReducibilityStatusCore env n with
            | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"))]
      IO.println ("ROOT " ++ (Json.mkObj [("module", toJson home.toString), ("name", ident n), ("kind", toJson (kindOf c)),
        ("type_refs", toJson (refs c.type)), ("value_refs", toJson valueRefs), ("own_type_refs", toJson ownTypeRefs),
        ("eqn_refs", toJson eqnRefs), ("flags", flags)]).compress)
  IO.println s!"CAT-COUNT {catCount}"
  for o in owners do
    IO.println s!"MODULE {o}: stored {rootCount[o]?.getD 0}"
