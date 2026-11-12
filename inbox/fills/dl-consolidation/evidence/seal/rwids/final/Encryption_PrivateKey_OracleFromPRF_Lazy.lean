import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.false_eq_true","Bool.not_eq_true","Function.update_of_ne","Function.update_self","List.getD_nil","List.length_ofFn","List.lookup_cons","Option.getD_none","Option.getD_some","Option.isSome_map","Option.isSome_none","Option.isSome_some","Option.map_none","Option.map_some","OracleComp.bind_assoc","OracleComp.pure_bind","ProbComp.expect_sample_update","addPt_eq","ctOf_eq","decAns_eq","expect_bind","expect_pure","expect_sample_comm","fImpl_challenge_none","fImpl_challenge_some","fImpl_dec","fImpl_enc","h","hU","hV","hd","hi2","hm","hne","hop'","hpad","hr","hst","hval","hx","hz0","hzb","if_false","if_neg","if_pos","lazyImpl_challenge_none","lazyImpl_challenge_some","lazyImpl_dec_closed","lazyImpl_dec_open","lazyImpl_enc","length_ctOf","look_flag","look_none","look_some","ofFn_padFin_of_length","ovr_addPt_of_isSome","ovr_addPt_of_none","ovr_apply","ovr_record_of_some","padAt_ctOf","padAt_eq","padFin_def","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","rStar_ctOf","rStar_eq","simulate_pure","simulate_query","this","zeroBits_apply","zipWith_xor_cancel_left"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy

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
