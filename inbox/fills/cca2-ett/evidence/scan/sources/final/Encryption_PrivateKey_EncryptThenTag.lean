import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open ETTGame ProbComp

def idsToCheck : List String := ["Bool.and_eq_true","Bool.not_eq_false","ChallengeSim.expect_sample_prod","EnsembleLemmas.ofFn_coinsEquiv","Equiv.apply_symm_apply","Equiv.trans_apply","Fin.cons_succ","Fin.cons_zero","FixedLengthScheme.decAnswer_none","FixedLengthScheme.decAnswer_some","FixedLengthScheme.encryptAt_eq","FixedLengthScheme.inLens_one","FixedLengthScheme.inLens_two","FixedLengthScheme.inLens_zero","FixedLengthScheme.outLens_one","FixedLengthScheme.outLens_two","FixedLengthScheme.outLens_zero","Function.comp_apply","List.append_nil","List.cons.injEq","List.drop_left'","List.length_append","List.length_cons","List.length_ofFn","List.length_replicate","List.length_zipWith","List.ofFn_succ","List.replicate_zero","List.take_left'","List.zipWith_cons_cons","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coinsEquivPoly_ofFn","NUPPT.coins_ofPolyTimeUniform","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Nat.cast_mul","Nat.min_self","Nat.sub_self","PRFGame.decOpen_atkOf","PRFGame.pkDin_two","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","abs_of_nonneg","accept_cca_indGame","accept_indGame_eq","add_zero","advantage_eq","ccaDecFun","ccaDecFun_eq","ccaDecOK","ccaDecOK_eq","ccaEncFun","ccaGenFun","ccaKeyEq","ccaMaskFun","ccaNonceEq","ccaScheme_ctLen","ccaScheme_dec","ccaScheme_enc","ccaScheme_gen","cca_ctLen_eval","cca_gen_runAt","ctW_eq","decL_eq","decide_eq_true_eq","decodeFin_eq","decodeFin_ofFn","dif_neg","div_eq_mul_inv","encW_eq","ettAcc_eq","ettCt_eval","ettDin_one","ettDin_two","ettDin_zero","ettDout_one","ettDout_two","ettDout_zero","expect_sample_equiv","h","hA","hB","hC₀","hC₁","hD","hFE","ha","hb","hc","hc₁","hdec","he","hk","hnok","hp","hr","ht","htag","hx","hρ","if_neg","if_pos","inv_pow","length_encW","length_pairEncode","maskL_eq","ofFn_arrowCongr_finCongr","ofFn_padFin_of_length","ofFn_zeroBits","pairFstD_pairEncode","pairSndD_pairEncode","pairV_eq","runAt_ccaDec","runAt_ccaEnc","runAt_ccaGen","sq","tagL_eq","validW_eq","wC_eq","wR_eq","wT_eq","wfW_eq","zipWith_xor_xor_self'"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag

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
