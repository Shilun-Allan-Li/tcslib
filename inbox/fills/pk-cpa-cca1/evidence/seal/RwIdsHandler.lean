import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command

/-! Explicit readings of the pk-cpa-cca1 fill in `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean`: every identifier the added lines pass
to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in
the file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.and_eq_true","Bool.false_eq_true","Collection.ofFn_padFin_of_le","EnsembleLemmas.blocks_apply","EnsembleLemmas.padL_eq","Equiv.trans_apply","Fin.coe_cast","Function.comp_apply","GGMRed.ofFn_padFin_of_length","GGMRed.pairEncode_append_right","InteractiveHandler.call_eq","InteractiveHandler.finInput_eq","InteractiveHandler.finish_eq","InteractiveHandler.impl_apply","InteractiveHandler.input_eq","List.cons_append","List.drop_succ_cons","List.drop_zero","List.getElem_drop","List.getElem_ofFn","List.getElem_take","List.headD_cons","List.headD_nil","List.length_cons","List.length_drop","List.length_ofFn","List.length_replicate","List.length_take","List.length_zipWith","List.nil_append","List.ofFn_fin_append","List.replicate_succ","List.take_left'","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","Nat.min_self","Nat.mul_comm","Nat.succ_mul","Option.isSome_none","OracleComp.pure_bind","OracleComp.query_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PrefixByLength.drop_def","and_self","bitCodec_encodeEntry","buildComp_succ_of_query","buildComp_succ_of_ret","buildComp_zero_of_ret","ctOf_eq","ctP","ctP_eval","decWF_eq","decide_eq_true_eq","encodeLog_one","finProdFinEquiv_apply_val","h","h0","h1","h2","hCnt","hFlag","hI","hL","hMsg","hRec","hS","hT","hU","hW","hWF","hX","hY","hans","hc","hcl","hct","hctOf","hlen","hn","hop","hpt","hrec","hwf.1","hwf.2","hx","hx0","hy","h₁","h₂","h₃","if_false","if_neg","if_true","length_ctOf","length_pairEncode","length_recBits","log_ne_nil","ofFn_padFin_eq_padL","ofFn_padFin_eq_take","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","pkDin_two","pkDin_zero","pkDout_one","pkDout_two","pkDout_zero","pkFin","pkHandler_finCall","pkHandler_outLen","pkHandler_perCall","pkOut_eq","pkRun","pkSeedTapes_eq","pkStLen_eq","pkState_eq","pkTapes","rCnt","rCt","rFlag","rI","rL","rMsg","rNew","rNew_fields","rNonce","rNonce_fields","rRec","rS","rU","rW","rWF","rX","rY","recBits_fields","recBits_none","recBits_some","replicate_one","replicate_two","replicate_zero'"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> pure []
    let env ← getEnv
    let modOf (c : Name) : String :=
      ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!.toString).getD "?"
    if cands.isEmpty then IO.println s!"{s}: (unresolved: local hypothesis or private)"
    else for c in cands do
      let k := match env.find? c with
        | some (.thmInfo _) => "theorem"
        | some (.defnInfo _) => "DEF"
        | some _ => "other"
        | none => "?"
      IO.println s!"{s}: {c}: {k} ({modOf c})"

end TCSlib.Cryptography.Composability.PRFGame
