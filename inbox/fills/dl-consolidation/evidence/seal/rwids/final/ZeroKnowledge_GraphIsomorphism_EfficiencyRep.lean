import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
open Lean Elab Command

namespace TCSlib.Cryptography.GI
open Complexity Turing Complexity.StateLoop

def idsToCheck : List String := ["BinArith.length_mulU","Bool.and_assoc","Bool.decide_and","Bool.decide_eq_true","Bool.false_eq_true","Bool.or_eq_false_iff","Bool.or_eq_true","Bool.true_and","Fin.forall_iff","Fin.val_mk","Function.comp_apply","Function.iterate_one","Function.iterate_succ_apply","Function.iterate_succ_apply'","Function.iterate_zero","List.drop_drop","List.drop_eq_nil_iff","List.drop_one","List.drop_succ_cons","List.drop_zero","List.getLast?_eq_getElem?","List.getLastD_eq_getLast?","List.head?_drop","List.headD_cons","List.headD_eq_head?","List.length_drop","List.length_nil","List.length_replicate","List.length_singleton","List.replicate_succ","List.replicate_zero","Nat.forall_lt_succ_right","Nat.one_mul","Nat.succ_mul","Nat.zero_add","Nat.zero_mul","Option.getD_none","Option.getD_some","Option.map_none","Option.map_some","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_normal","PolyExpr.eval_var","Strategy.encodeMsgs_cons","Strategy.pairFstD_encodeMsgs","Turing.pairEncode_ne_nil","argM_ilayout","argX_ilayout","coinBlock_eq","decPerm_encPerm","decide_eq_false_iff_not","decide_eq_true_eq","decide_not","encodeMsgs_eq_nil_iff","gniBlock","gniBlock_eval","gniIter_eq","gniStep","gniVerifierRep_next","h1","h2","halfCount_encodeMsgs","hb","headD_drop","headD_take","hj","hk'","horbit","hs","hs'","hw","hz","id_eq","if_false","if_neg","if_pos","if_true","ih","inCoins_ilayout","inParam_ilayout","iterate_pairSndD_encodeMsgs","iterate_sndD_two_encodeMsgs","lastSteps","lastSteps_encodeMsgs","length_pairEncode","msgCount","msgCount_encodeMsgs","not_false_eq_true","orbit_succ","pairDecode_pairEncode","pairFstD_eq","pairFstD_pairEncode","pairSndD_encodeMsgs","pairSndD_eq","pairSndD_pairEncode","peelStepsAux","relabelAt_replicate","sampleStr_eq","true_and","vcount_ilayout"]
def scannedModule : Name := `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    if cands.isEmpty then IO.println s!"{s}\t-\tlocal/unresolved\t-"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some (.opaqueInfo _) => "opaque"
        | some (.inductInfo _) => "inductive"
        | some (.ctorInfo _) => "ctor"
        | some _ => "other"
        | none => "?"
      let m := modOf c
      let tag := if k == "DEF" then
          (if m == scannedModule then "own-def" else if (`TCSlib).isPrefixOf m then "FOREIGN-TCSLIB-DEF" else "core/mathlib-def")
        else k
      IO.println s!"{s}\t{c}\t{tag}\t{m}"

end TCSlib.Cryptography.GI
