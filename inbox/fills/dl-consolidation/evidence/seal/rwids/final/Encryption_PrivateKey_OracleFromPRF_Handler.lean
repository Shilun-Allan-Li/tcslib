import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt)

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.and_eq_true","Bool.false_eq_true","Collection.ofFn_padFin_of_le","EnsembleLemmas.blocks_apply","EnsembleLemmas.blocks_eq","EnsembleLemmas.ofFn_padFin_eq_padL","Equiv.trans_apply","Fin.val_one","FunFamily.ofFn_blocks","Function.comp_apply","GGMRed.pairEncode_append_right","InteractiveHandler.call_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.impl_apply","InteractiveHandler.rCnt_input","InteractiveHandler.rI_input","InteractiveHandler.rL_input","InteractiveHandler.rS_input","InteractiveHandler.rU_input","InteractiveHandler.rW_input","InteractiveHandler.rX_input","List.cons_append","List.drop_succ_cons","List.drop_zero","List.headD_cons","List.headD_nil","List.length_cons","List.length_ofFn","List.length_replicate","List.length_zipWith","List.nil_append","List.ofFn_fin_append","List.replicate_one","List.replicate_succ","List.take_left'","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","Nat.min_self","Option.isSome_none","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PrefixByLength.drop_def","and_self","bitCodec_encodeEntry","buildComp_succ_of_query","buildComp_zero_of_ret","ctOf_eq","ctP","ctP_eval","decWF_eq","decide_eq_true_eq","encodeLog_one","h0","h1","h2","hCnt","hFlag","hI","hL","hMsg","hRec","hS","hT","hU","hW","hWF","hX","hY","hans","hc","hcl","hct","hctOf","hlen","hn","hop","hrec","hwf.1","hwf.2","hx","hx0","hy","h₁","h₂","h₃","if_false","if_neg","if_true","length_ctOf","length_pairEncode","length_recBits","log_ne_nil","ofFn_arrowCongr_finCongr","ofFn_padFin_of_length","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","pkDin_two","pkDin_zero","pkDout_one","pkDout_two","pkDout_zero","pkFin","pkHandler_finCall","pkHandler_outLen","pkHandler_perCall","pkOut_eq","pkRun","pkSeedTapes_eq","pkStLen_eq","pkState_eq","pkTapes","rCt","rFlag","rMsg","rNew","rNew_fields","rNonce","rNonce_fields","rRec","rWF","rY","recBits_fields","recBits_none","recBits_some","replicate_two","replicate_zero'"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler

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

end TCSlib.Cryptography.Composability.PRFGame
