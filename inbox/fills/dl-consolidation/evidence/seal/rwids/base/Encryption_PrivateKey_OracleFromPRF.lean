import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open PRFGame ChallengeSim ProbComp

def idsToCheck : List String := ["AdaptiveCPA.headD_ofFn_one","Bool.and_eq_true","Bool.and_false","Bool.not_eq_eq_eq_not","Bool.not_not","Bool.not_true","Bool.true_and","Bool.xor_self","Bridge.acceptGame_eq","Bridge.acceptProb_eq","Equiv.trans_apply","Fin.cons_succ","Fin.cons_zero","FixedLengthScheme.INDSecure_iff","FixedLengthScheme.decAnswer_none","FixedLengthScheme.decAnswer_some","FixedLengthScheme.decOpen_cca2","FixedLengthScheme.encryptAt_eq","FixedLengthScheme.inLens_one","FixedLengthScheme.inLens_two","FixedLengthScheme.inLens_zero","FixedLengthScheme.indCodec_decodeMove","FixedLengthScheme.indCodec_encodeEntry","FixedLengthScheme.indGame_eq","FixedLengthScheme.indImpl_challenge_none_onSpec","FixedLengthScheme.indImpl_dec_onSpec","FixedLengthScheme.outLens_one","FixedLengthScheme.outLens_two","FixedLengthScheme.outLens_zero","FixedLengthScheme.splitHalf_fst","FixedLengthScheme.splitHalf_snd","Function.comp_apply","List.append_assoc","List.cons_append","List.drop_succ_cons","List.drop_zero","List.getLastD_concat","List.headD_cons","List.length_append","List.length_nil","List.length_ofFn","List.length_singleton","List.length_zipWith","List.nil_append","List.ofFn_const","List.ofFn_fin_append","List.ofFn_succ","List.ofFn_succ_last","List.replicate_one","List.replicate_succ'","List.reverse_append","List.reverse_cons","List.reverse_nil","List.reverse_reverse","List.singleton_append","List.zipWith_replicate","MachineCodec.encodeLog_cons","MachineCodec.encodeLog_nil","NUPPT.advInput_eq","NUPPT.coinsCongr_ofFn","NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn","NUPPT.inArg_eq","NUPPT.inParam_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","NUPPT.toComp_eq","Nat.min_self","Option.some.injEq","OracleComp.bind_assoc","OracleComp.pure_bind","PRFGame.atkOf_false","PRFGame.atkOf_true","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","ProbComp.prob_bind","ProbComp.prob_pure","abs_sub_comm","accept_eq","accept_prf_indGame","advantage_eq","buildComp_succ_of_query","buildComp_zero_of_ret","cast_cast","cast_eq","cca2Adversary","cca2Adversary_one","cca2Adversary_run","cca2Adversary_two","cca2Alter_ofFn","cca2CtLen","cca2Decrypt","cca2FlipBits_unmask","cca2FlipLast","cca2FlipLast_append","cca2FlipLast_length","cca2FlipLast_ofFn","cca2FlipLast_pair","cca2FlipLast_snoc","cca2Messages","cca2Messages_choice","cca2Messages_ofFn","cca2Next","cca2OfFn_cast","ctOf_eq","ctP_eval","decOpen_atkOf","decWF_eq","decide_eq_false_iff_not","decide_eq_true_eq","decodeFin_ofFn","decodeFin_runAt_prfDec_of_not_wf","distAdv_def","div_one","eq_pairEncode_of_pairFstD_ne","expect_sample_equiv","expect_simulate_congr","h","h1","hA","hFE","hQ","hacc","hb","hc","hcc","hk","hlast","hn","hv","hw","hw.2","hx","hxc","if_neg","if_pos","indCodec_eq_bitCodec","inv_pow","ite_false","ite_true","length_pairEncode","negligible_iff","ofFn_arrowCongr_finCongr","ofFn_prfKeyEq","ofFn_zeroBits","oracleDist_apply","pairEncode_eq","pairFstD_pairEncode","pairSndD_pairEncode","pkDin_one","pkDin_two","pkDin_zero","pkDout_one","pkDout_two","pkDout_zero","pow_zero","prfAdv_def","prfAdv_prfReduction","prfFixedScheme_ctLen","prfFixedScheme_dec","prfFixedScheme_enc","prfFixedScheme_gen","prfKeyEq","prfNonceEq","prfScheme_dec","prfScheme_enc","prfScheme_gen","prf_ctLen_eval","prf_gen_runAt","prob_bind","prob_pure","randomFunction_apply","runAt_coinKey","runAt_prfDec","runAt_prfEnc","simulate_pure","simulate_query","zipWith_xor_ofFn_add"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF

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

end TCSlib.Cryptography.Composability
