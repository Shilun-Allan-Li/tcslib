import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
open Lean Elab Command

/-! Explicit readings of the padded-cpa fill in `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean`: every identifier the added lines pass to
`rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp

def idsToCheck : List String := ["BitPublicKeyScheme.padded_ctLen","BitPublicKeyScheme.padded_msgLen","BitPublicKeyScheme.pkEncDist_eq","Bool.decide_eq_true","Bool.false_eq_true","Bridge.acceptGame_eq","Bridge.acceptProb_eq","FixedLengthPKScheme.INDSecure_iff","FixedLengthPKScheme.inLens_one","FixedLengthPKScheme.inLens_zero","FixedLengthPKScheme.indGame_eq","FixedLengthPKScheme.outLens_one","FixedLengthPKScheme.outLens_zero","FixedLengthScheme.splitHalf_fst","FixedLengthScheme.splitHalf_snd","Function.comp_apply","List.cons.injEq","List.getD_cons_succ","List.getD_cons_zero","List.headD_cons","List.length_replicate","List.ofFn_succ","List.ofFn_zero","NUPPT.distinguisherL_eq","Option.elim_none","Option.elim_some","OracleComp.bind_assoc","OracleComp.pure.injEq","OracleComp.pure_bind","PolyExpr.eval_const","PolyHandler.advInput_eq","PolyHandler.result_eq","Prod.mk.injEq","S.indImpl_challenge_none","S.indImpl_challenge_repeat","S.indImpl_dec_cpa","accept_eq","advantage_eq","and_true","chRun_pure","chRun_query_one_none","chRun_query_one_some","chRun_query_zero","cpaAns","cpaAns_seedIn","distAdv_def","expect_bind","expect_pure","expect_sample_comm","expect_sample_equiv","expect_sample_prod","expect_sample_unique","expect_sub","hD","hG","ha","hadv","hans","hmm","hpt","hq'","hrun","hs'","hsim","h₁","h₂","if_false","if_true","ih","length_of_firstQ_eq_some","length_pairEncode","ofFn_splitHalf_bit","padCt_eq","pairFstD_pairEncode","pairSndD_pairEncode","prob_bind","prob_pure","recAdvIn_eq","recDin_one","recDin_zero","recDout_one","recDout_zero","recHandler_advIn","recHandler_out","recHandler_seedLen","recOut_init","recOut_recorded","seedIn_eq","simulate_pure","simulate_query","sub_self"]

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
