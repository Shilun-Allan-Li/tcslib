import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command

/-! Explicit readings of the pk-cpa-cca1 fill in `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Reduction.lean`: every identifier the added lines pass
to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in
the file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["AdaptiveCPA.headD_ofFn_one","Bool.and_eq_true","Bool.false_and","Bool.not_eq_true","Bool.true_and","FixedLengthScheme.decOpen_cca1","FixedLengthScheme.decOpen_cpa","GGMRed.ofFn_padFin_of_length","InteractiveHandler.advInput_eq","List.getD_nil","List.length_ofFn","NUPPT.toComp_eq","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","QueryImpl.comp_apply","QueryImpl.ofComp_apply","atkOf","decAns_eq","decOpen_atkOf","decWF_eq","decide_eq_true_eq","eval_toOracleAdversary_width","expect_bind","expect_eImpl","expect_pure","expect_sample_comm","expect_sample_equiv","expect_sample_prod","fOuter","fOuter_apply","fOuter_tape","h","h2","hQ","hT","hn","hop","hrun","hwf'.1","hx0","hz","hφ₀","hφ₄","h₁","h₂","if_neg","if_pos","key","ofFn_evalFn_toCompOn","padFin_def","padFin_ofFn","pkAbs_eq","pkHState_eq","pkHandler_finCall","pkHandler_finish","pkHandler_impl_challenge_none","pkHandler_impl_challenge_some","pkHandler_impl_dec_closed","pkHandler_impl_dec_open","pkHandler_impl_enc","pkHandler_init_hstate","pkHandler_outLen","pkHandler_perCall","pkOut_eq","qRed","qRed_eval","simulate_bind","simulate_comp","simulate_eq_of_abs_bounded","simulate_pure","simulate_query","zeroBits_apply"]

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
