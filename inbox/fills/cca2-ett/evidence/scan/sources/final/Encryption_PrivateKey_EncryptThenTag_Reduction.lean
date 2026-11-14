import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["AdaptiveCPA.extTape_of_lt","AdaptiveCPA.msgOf_eq","Bool.and_eq_true","Bool.and_false","Bool.and_true","Bool.false_and","Bool.false_eq_true","Bool.not_eq_true","Bool.not_false","Bool.not_true","Bool.true_and","Bool.true_or","Bridge.acceptGame_eq","Bridge.acceptProb_eq","ChallengeSim.expect_sample_prod","List.length_append","List.length_ofFn","OracleComp.bind_assoc","OracleComp.pure_bind","PRFGame.ofFn_evalFn_toCompOn","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_subst","PolyExpr.eval_var","QueryImpl.comp_apply","QueryImpl.ofComp_apply","accept_eq","dAbs_eq","dHandler_advInput","dHandler_finCall","dHandler_finish","dHandler_impl_challenge_none","dHandler_impl_challenge_some","dHandler_impl_dec_nwf","dHandler_impl_dec_ref","dHandler_impl_dec_wf","dHandler_impl_enc","dHandler_init_hstate","dHandler_outLen","dHandler_perCall","dTape_eq","dTapes_eq","dTapes_of_lt","decAnsW_eq","decide_eq_true_eq","distAdv_def","e1","encW_eq","ettAcc_eq","ettDin_two","ettDin_zero","ettStep_challenge_none","ettStep_challenge_some","ettStep_dec","ettStep_enc","eval_toOracleAdversary_len","expect_bind","expect_ettTape","expect_pure","expect_sample_comm","expect_sample_equiv","gOuter","gOuter_apply","gOuter_pair","h2","hA₁","hD","hQ","hc","headD_ofFn_one","hq₂","hr","href","hrun","hwf","hx","hφ₀","hφ₄","if_false","if_neg","if_pos","key","ofFn_padFin_of_length","oracleDist_apply","pairV_eq","prfAdv_def","prfAdv_eq_expect","prob_bind","prob_pure","randomFunction_apply","show","simulate_bind","simulate_comp","simulate_eq_of_abs_bounded","simulate_pure","simulate_query","tagL_eq","tagLen_eval","tagOut_eq","validW_eq","wfW_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Reduction

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
