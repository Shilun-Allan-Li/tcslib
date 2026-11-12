import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command

/-! Explicit readings of the pk-cpa-cca1 fill in `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Transfer.lean`: every identifier the added lines pass
to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in
the file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","AdaptiveCPA.ofFn_cast","AdaptiveCPA.padFin_ofFn_zeroBits","Bool.and_eq_true","Bool.false_and","Bool.not_eq_true","Bool.true_and","GGMRed.ofFn_padFin_of_length","List.length_cons","List.length_ofFn","List.length_zipWith","Nat.min_self","S.inLens_two","S.inLens_zero","S.indImpl_challenge_none_onSpec","S.indImpl_challenge_repeat_onSpec","S.indImpl_dec_onSpec","S.indImpl_enc_onSpec","S.outLens_one","S.outLens_two","S.outLens_zero","decAns_eq","decOpen_atkOf","decWF_eq","decide_eq_true_eq","expect_bind","expect_pure","expect_sample_equiv","fImpl_challenge_none","fImpl_challenge_some","fImpl_dec","fImpl_enc","hc","hct","hd","hdec","he","henc","henc'","hlenCt","hm","hm'","hmm","hop","hsel","ht","hw.2","if_neg","if_pos","length_ctOf","ofFn_zeroBits","padFin_nil","this"]

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
