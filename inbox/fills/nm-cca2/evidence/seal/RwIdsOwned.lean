import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
open Lean Elab Command

/-! Explicit readings of the nm-cca2 fill in `TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Indistinguishability.lean`: every identifier the added lines pass to `rw`,
`rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp`, `unfold` or `delta`, resolved in the
file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games AdaptiveCPA NMCCA2 ProbComp ChallengeSim


def idsToCheck : List String := ["Bool.not_false","Bool.not_true","Bool.true_and","EnsembleLemmas.length_padL","EnsembleLemmas.padL_eq","Equiv.trans_apply","FixedLengthScheme.decOpen_cca2","GGMRed.ofFn_padFin_of_length","INDSecure_iff","List.drop_left'","List.drop_zero","List.getElem_drop","List.getElem_map","List.getElem_ofFn","List.getElem_range","List.getElem_take","List.headD_cons","List.length_append","List.length_drop","List.length_map","List.length_ofFn","List.length_range","List.length_singleton","List.length_take","List.take_append_of_le_length","List.take_left'","List.take_of_length_le","NMSecure_iff","NUPPT.coinsEquivPoly_ofFn","NUPPT.distinguisherL_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","Nat.mul_comm","Nat.one_mul","Nat.succ_mul","Nat.zero_mul","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","S.enc_length","S.indGame_eq","S.nmDecrypt_eq","S.nmGame_eq","S.outLens_zero","acDin_zero","acDout_zero","accept_eq","advantage_eq","advantage_self","castImpl_eq","decAnswers_eq_nmOutput","decBlock_eq","decBlock_eq_nthCt","decHandler_advInput","decHandler_outLen","decide_eq_false","decide_eq_true","encCt_eq","encHandler_advInput","encHandler_finish","encHandler_outLen","expect_bind","expect_pure","expect_sample_comm","expect_sample_equiv","expect_sample_prod","finProdFinEquiv_apply_val","guessDist_distinguisherL","guessDist_nmOutput","h1","h2","hB'","hW","ha","hblk","hc","hct","hd1","hdecB","headD_ofFn_one","hg","hi","hin","hlen","hout","hw","hφ","if_neg","if_pos","indCodec_eq_bitCodec","indImpl_dec_onSpec_cast","indImpl_eq_of_msgLen_eq_zero","key","nmCodec_eq_bitCodec","nmOutput_eq","ofFn_cast","ofFn_nthCt","ofFn_padFin_eq_take","ofFn_zeroBits","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","prob_bind","prob_pure","simulate_bind","simulate_decHandler_finish","simulate_decHandler_impl","simulate_encHandler_impl","simulate_pure"]

#eval show CommandElabM Unit from do
  for s in idsToCheck do
    let s' := if s.startsWith "S." then "FixedLengthPKScheme." ++ (s.drop 2) else s
    let n := s'.toName
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

end TCSlib.Cryptography.Composability.FixedLengthPKScheme
