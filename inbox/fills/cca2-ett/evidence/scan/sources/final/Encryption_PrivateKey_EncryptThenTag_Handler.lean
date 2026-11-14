import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt rAns)

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.and_eq_true","Bool.false_eq_true","Bool.true_and","Collection.ofFn_padFin_of_le","EnsembleLemmas.ofFn_padFin_eq_padL","Fin.val_one","Fin.val_zero","Function.comp_apply","GGMRed.pairEncode_append_right","InteractiveHandler.advInput_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.rAns_eq","InteractiveHandler.rCnt_input","InteractiveHandler.rW_input","List.cons_append","List.drop_append","List.drop_eq_nil_of_le","List.drop_succ_cons","List.drop_zero","List.headD_cons","List.headD_nil","List.length_append","List.length_cons","List.length_ofFn","List.length_replicate","List.length_zipWith","List.nil_append","List.replicate_add","List.replicate_one","List.replicate_succ","List.replicate_zero","List.take_left'","Nat.add_sub_cancel_left","Nat.min_self","Option.isSome_none","Option.isSome_some","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PrefixByLength.drop_def","ctW_eq","dFin","dHandler_finCall","dHandler_outLen","dHandler_perCall","dRun","dSeedLen","dStLen_eq","dState_eq","dTape_eq","decL_eq","decide_eq_false_iff_not","decide_eq_true_eq","decide_true","ettCt","ettCt_eval","ettDin_two","ettDin_zero","ettDout_one","ettDout_two","ettDout_zero","h0","hCnt","hFE","hFlag","hI","hK","hL","hMsg","hN","hRec","hRef","hS","hU","hW","hWF","hX","hY","hans","hc","hcnt","hct","hlen","hr","hrec","href","ht","hwf","hwf'.1","hwf'.2","hx","h₁","h₂","h₃","if_false","if_neg","if_pos","if_true","length_ctW_tag","length_pairEncode","length_recBits","log_ne_nil","maskL_eq","mask_eval","ofFn_dHSeed","ofFn_dHState","ofFn_padFin_of_length","ofFn_padFin_pair","ofFn_zeroBits","padFin_nil","pairFstD_pairEncode","pairSndD_pairEncode","rCt","rDec","rFlag","rKey","rMask","rMsg","rNew","rNew_fields","rNonce","rOK","rRec","rRef","rWF","rZero","rZero_fields","recBits_fields","recBits_none","recBits_some","refW_none","refW_some","show","tagLen","tagLen_eval","tagOut_eq","wC_eq","wR_eq","wT_eq","wfW_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Handler

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

end TCSlib.Cryptography.Composability.ETTGame
