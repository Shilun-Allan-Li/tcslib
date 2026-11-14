import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Transfer
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.ETTGame
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["AdaptiveCPA.msgOf_eq","Bool.and_eq_true","Bool.and_true","Bool.not_eq_true","Bool.not_false","Bool.true_and","Bool.true_or","FixedLengthScheme.decOpen_cca2","FixedLengthScheme.indCodec_eq_bitCodec","FixedLengthScheme.indGame_eq","List.length_cons","List.length_ofFn","List.length_zipWith","Nat.min_self","Option.some.injEq","S.inLens_two","S.inLens_zero","S.indImpl_challenge_none_onSpec","S.indImpl_challenge_repeat_onSpec","S.indImpl_dec_onSpec","S.indImpl_enc_onSpec","S.outLens_one","S.outLens_two","S.outLens_zero","accept_eq","decAnsW_eq","decL_eq","decide_eq_true_eq","ettImpl_apply","ettStep_challenge_none","ettStep_challenge_some","ettStep_dec","ettStep_enc","expect_bind","expect_const","expect_pure","expect_sample_equiv","h","h1","hc","hct","hdec","headD_ofFn_one","henc","henc'","hlenEnc","hm","hm'","hmm","hr","href","hsel","hv.1.2","if_neg","if_pos","length_encW","ofFn_cast","ofFn_padFin_of_length","ofFn_zeroBits","padFin_nil","prob_bind","prob_pure","refW_none","refW_some","stRec_eq","this","validW_eq","wfW_eq"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Transfer

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
