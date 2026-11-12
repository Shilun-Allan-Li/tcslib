import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open ChallengeSim ProbComp
open TCSlib.Cryptography.Composability.FixedLengthPKScheme

def idsToCheck : List String := ["BinArith.hasFalse_eq","BitPublicKeyScheme.padded_ctLen","BitPublicKeyScheme.padded_msgLen","BitPublicKeyScheme.pkEncDist_eq","Bool.and_eq_true","Bool.decide_eq_true","Bool.false_and","Bool.false_eq_true","Bool.not_eq_true'","Bridge.acceptGame_eq","Bridge.acceptProb_eq","FixedLengthPKScheme.INDSecure_iff","FixedLengthPKScheme.inLens_one","FixedLengthPKScheme.inLens_zero","FixedLengthPKScheme.indGame_eq","FixedLengthPKScheme.outLens_one","FixedLengthPKScheme.outLens_zero","FixedLengthScheme.decOpen_cca2","FixedLengthScheme.decOpen_cpa","FixedLengthScheme.splitHalf_fst","FixedLengthScheme.splitHalf_snd","Function.comp_apply","List.any_eq_false","List.cons.injEq","List.getD_cons_succ","List.getD_cons_zero","List.headD_cons","List.length_ofFn","List.length_replicate","List.length_singleton","List.mem_map","List.ofFn_succ","List.ofFn_zero","NUPPT.advInput_eq","NUPPT.coinsCongr_ofFn","NUPPT.distinguisherL_eq","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Option.elim_none","Option.elim_some","OracleComp.pure.injEq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PolyHandler.advInput_eq","PolyHandler.result_eq","Prod.mk.injEq","PublicKeyScheme.padded_enc","S.correct","S.inLens_one","S.inLens_zero","S.indImpl_dec_onSpec","S.indSpec_dom","S.indSpec_rng","S.outLens_one","accept_eq","advantage_eq","and_imp","and_true","cast_eq","cpaAns","cpaAns_seedIn","decide_eq_true_eq","decodeFin_ofFn","distAdv_def","expect_sample_comm","expect_sample_equiv","expect_sample_prod","expect_sample_unique","expect_sub","forall_exists_index","hD","hG","ha","hadv","hall","hans","henc.runAt_eq","hlen","hm","hmm","hpt","hq'","hrun","hs'","hsim","hw","h₁","h₂","id_eq","if_false","if_true","indImpl","isPadded","isPadded_padCt","length_of_firstQ_eq_some","length_pairEncode","ofFn_splitHalf_bit","padCt","padCt_eq","padDecFun","padDecFun_padCt","padEncFun","padEncFun_eq","padEnc_coins","pairFstD_pairEncode","pairSndD_pairEncode","prob_bind","prob_pure","recAdvIn_eq","recDin_one","recDin_zero","recDout_one","recDout_zero","recHandler_advIn","recHandler_out","recHandler_seedLen","recOut_init","recOut_recorded","runAt_padEnc","seedIn_eq","show","sub_self"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

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
