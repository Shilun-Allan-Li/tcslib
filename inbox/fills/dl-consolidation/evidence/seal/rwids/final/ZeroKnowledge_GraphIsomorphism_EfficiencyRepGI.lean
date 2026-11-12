import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI
open Lean Elab Command

namespace TCSlib.Cryptography.GI
open Complexity Turing Complexity.StateLoop

def idsToCheck : List String := ["Bool.and_assoc","Bool.decide_and","Bool.decide_eq_true","Bool.true_and","Fin.forall_iff","Fin.val_mk","Function.comp_apply","Function.iterate_one","Function.iterate_succ_apply'","Function.iterate_zero","List.drop_drop","List.drop_eq_nil_iff","List.drop_one","List.headD_cons","List.length_drop","List.length_replicate","List.length_singleton","List.tail_drop","Nat.forall_lt_succ_right","Nat.zero_add","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_normal","PolyExpr.eval_var","Strategy.pairFstD_encodeMsgs","argM_ilayout","argX_ilayout","argZ_ilayout","decPerm_encPerm","decide_eq_true_eq","decide_not","encodeMsgs_eq_nil_iff","giBlock","giBlock_eval","giIter_eq","giProverRep_next","giStep","halfCount_encodeMsgs","halfRem_ne_nil_iff","halfRem_nil_iff","hb","headD_drop","id_eq","if_neg","if_pos","ih","inCoins_ilayout","inParam_ilayout","iterate_sndD_two_encodeMsgs","lastMsg_encodeMsgs","length_pairEncode","msgCount_encodeMsgs","mulInvStr_encPerm","pairFstD_pairEncode","pairSndD_encodeMsgs","pairSndD_pairEncode","relabelAt_replicate","sampleStr_eq","vcount_ilayout"]
def scannedModule : Name := `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI

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
