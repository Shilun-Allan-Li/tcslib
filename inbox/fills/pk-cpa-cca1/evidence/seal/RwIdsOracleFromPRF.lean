import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command

/-! Explicit readings of the pk-cpa-cca1 fill in `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean`: every identifier the added lines pass
to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in
the file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games PRFGame ChallengeSim ProbComp

def idsToCheck : List String := ["AdaptiveCPA.headD_ofFn_one","Bool.and_eq_true","Bool.and_false","Bool.not_true","Bridge.acceptGame_eq","Bridge.acceptProb_eq","Equiv.trans_apply","Fin.cons_succ","Fin.cons_zero","FixedLengthScheme.INDSecure_iff","FixedLengthScheme.decAnswer_none","FixedLengthScheme.decAnswer_some","FixedLengthScheme.encryptAt_eq","FixedLengthScheme.inLens_one","FixedLengthScheme.inLens_two","FixedLengthScheme.inLens_zero","FixedLengthScheme.indGame_eq","FixedLengthScheme.outLens_one","FixedLengthScheme.outLens_two","FixedLengthScheme.outLens_zero","List.length_nil","List.length_ofFn","List.length_zipWith","List.ofFn_succ","NUPPT.coinsCongr_ofFn","NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn","Nat.min_self","PRFGame.atkOf_false","PRFGame.atkOf_true","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","abs_sub_comm","accept_eq","accept_prf_indGame","advantage_eq","ctOf_eq","ctP_eval","decOpen_atkOf","decWF_eq","decide_eq_true_eq","decodeFin_ofFn","decodeFin_runAt_prfDec_of_not_wf","distAdv_def","div_one","eq_pairEncode_of_pairFstD_ne","expect_sample_equiv","expect_simulate_congr","h","h1","hFE","hQ","hk","hv","hw.2","hx","if_neg","if_pos","indCodec_eq_bitCodec","inv_pow","length_pairEncode","ofFn_arrowCongr_finCongr","ofFn_prfKeyEq","ofFn_zeroBits","oracleDist_apply","pkDin_one","pkDin_two","pkDin_zero","pkDout_one","pkDout_two","pkDout_zero","pow_zero","prfAdv_def","prfAdv_prfReduction","prfFixedScheme_ctLen","prfFixedScheme_dec","prfFixedScheme_enc","prfFixedScheme_gen","prfKeyEq","prfNonceEq","prfScheme_dec","prfScheme_enc","prfScheme_gen","prf_ctLen_eval","prf_gen_runAt","prob_bind","prob_pure","randomFunction_apply","runAt_prfDec","runAt_prfEnc"]

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

end TCSlib.Cryptography.Composability
