import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.PRFGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","AdaptiveCPA.ofFn_cast","AdaptiveCPA.padFin_ofFn_zeroBits","Bool.and_eq_true","Bool.false_and","Bool.not_eq_true","Bool.true_and","GGMRed.ofFn_padFin_of_length","List.length_cons","List.length_ofFn","List.length_zipWith","Nat.min_self","S.inLens_two","S.inLens_zero","S.indImpl_challenge_none_onSpec","S.indImpl_challenge_repeat_onSpec","S.indImpl_dec_onSpec","S.indImpl_enc_onSpec","S.outLens_one","S.outLens_two","S.outLens_zero","decAns_eq","decOpen_atkOf","decWF_eq","decide_eq_true_eq","expect_bind","expect_pure","expect_sample_equiv","fImpl_challenge_none","fImpl_challenge_some","fImpl_dec","fImpl_enc","hc","hct","hd","hdec","he","henc","henc'","hlenCt","hm","hm'","hmm","hop","hsel","ht","hw.2","if_neg","if_pos","length_ctOf","ofFn_zeroBits","padFin_nil","this"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer

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
