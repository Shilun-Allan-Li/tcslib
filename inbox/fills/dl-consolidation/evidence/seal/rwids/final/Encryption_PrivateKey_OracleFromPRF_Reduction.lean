import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["Bool.and_eq_true","Bool.false_and","Bool.not_eq_true","Bool.true_and","FixedLengthScheme.decOpen_cca1","FixedLengthScheme.decOpen_cpa","InteractiveHandler.advInput_eq","List.getD_nil","List.length_ofFn","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","QueryImpl.comp_apply","QueryImpl.ofComp_apply","atkOf","decAns_eq","decOpen_atkOf","decWF_eq","decide_eq_true_eq","eval_toOracleAdversary_width","expect_bind","expect_eImpl","expect_pure","expect_sample_comm","expect_sample_equiv","expect_sample_prod","fOuter","fOuter_apply","fOuter_tape","h","h2","hQ","hT","headD_ofFn_one","hn","hop","hrun","hwf'.1","hx0","hz","hφ₀","hφ₄","if_neg","if_pos","key","ofFn_evalFn_toCompOn","ofFn_padFin_of_length","padFin_def","padFin_ofFn","pkAbs_eq","pkHState_eq","pkHandler_finCall","pkHandler_finish","pkHandler_impl_challenge_none","pkHandler_impl_challenge_some","pkHandler_impl_dec_closed","pkHandler_impl_dec_open","pkHandler_impl_enc","pkHandler_init_hstate","pkHandler_outLen","pkHandler_perCall","pkOut_eq","qRed","qRed_eval","show","simulate_bind","simulate_comp","simulate_eq_of_abs_bounded","simulate_pure","simulate_query","zeroBits_apply"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction

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
