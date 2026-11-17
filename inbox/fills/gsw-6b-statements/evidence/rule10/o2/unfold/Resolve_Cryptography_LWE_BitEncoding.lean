import TCSlib.Cryptography.LWE.BitEncoding
namespace TCSlib.Cryptography.LWE.BitEncoding
open Lean in
run_cmd do
  let env ← getEnv
  let cns ← Lean.getCurrNamespace
  let ods ← Lean.getOpenDecls
  for s in (["Bool.false_eq_true", "Int.natAbs_natCast", "Nat.cast_add", "Nat.cast_sub", "ZMod.natAbs_valMinAbs_neg", "ZMod.natCast_self", "ZMod.natCast_zmod_val", "ZMod.valMinAbs_def_pos", "ZMod.valMinAbs_natCast_of_le_half", "ZMod.val_natCast_of_lt", "ZMod.val_sub", "add_sub_add_right_eq_sub", "add_zero", "codepoint_eq", "decide_eq_true_iff", "decodeHi_eq", "decodeLo_eq", "decode_eq", "distance_codepoints", "distance_eq", "distance_symm", "habs", "hcast", "hsub", "if_false", "if_true", "neg_sub", "sub_add_sub_cancel", "sub_zero", "zero_sub"] : List String) do
    let id := s.toName
    let cands := (Lean.ResolveName.resolveGlobalName env (← Lean.getOptions) cns ods id).filter (·.2.isEmpty) |>.map (·.1)
    let mut arr : Array Json := #[]
    for n in cands do
      let some ci := env.find? n | continue
      let kind := match ci with
        | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      let home := match env.getModuleIdxFor? n with
        | some mi => env.header.moduleNames[mi.toNat]!.toString | none => "<this file>"
      let st := match Lean.getReducibilityStatusCore env n with
        | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
      let abbrevFlag := match ci with
        | .defnInfo d => match d.hints with | .abbrev => true | _ => false
        | _ => false
      arr := arr.push (Json.mkObj [("name", toJson n.toString), ("kind", toJson kind), ("home", toJson home),
        ("status", toJson st), ("abbrev", toJson abbrevFlag), ("instance", toJson (Lean.Meta.isInstanceCore env n)),
        ("matcher", toJson (Lean.Meta.isMatcherCore env n)), ("projection", toJson (env.isProjectionFn n))])
    IO.println ("RESOLVE " ++ (Json.mkObj [("ident", toJson s), ("cands", Json.arr arr)]).compress)
