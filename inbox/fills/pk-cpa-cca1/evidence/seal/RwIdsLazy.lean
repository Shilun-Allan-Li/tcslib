import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
open Lean Elab Command

/-! Explicit readings of the pk-cpa-cca1 fill in `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Lazy.lean`: every identifier the added lines pass
to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`, resolved in
the file's namespace with its `open`s. A definition may be passed only when it is the file's own. -/

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","BitwiseSim.expect_sample_update","Bool.false_eq_true","Bool.not_eq_true","Function.update_of_ne","Function.update_self","GGMRed.ofFn_padFin_of_length","List.getD_nil","List.getElem_zipWith","List.length_ofFn","List.lookup_cons","Option.getD_none","Option.getD_some","Option.isSome_map","Option.isSome_none","Option.isSome_some","Option.map_none","Option.map_some","OracleComp.bind_assoc","OracleComp.pure_bind","addPt_eq","ctOf_eq","decAns_eq","expect_bind","expect_pure","expect_sample_comm","fImpl_challenge_none","fImpl_challenge_some","fImpl_dec","fImpl_enc","h","hU","hV","hd","hi2","hm","hne","hop'","hpad","hr","hst","hval","hx","hz0","hzb","if_false","if_neg","if_pos","lazyImpl_challenge_none","lazyImpl_challenge_some","lazyImpl_dec_closed","lazyImpl_dec_open","lazyImpl_enc","length_ctOf","look_flag","look_none","look_some","ovr_addPt_of_isSome","ovr_addPt_of_none","ovr_apply","ovr_record_of_some","padAt_ctOf","padAt_eq","padFin_def","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","rStar_ctOf","rStar_eq","simulate_pure","simulate_query","this","zeroBits_apply","zipWith_xor_cancel_left"]

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
