import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
open Lean Elab Command

namespace TCSlib.Cryptography.Composability.AdaptiveCPA
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

def idsToCheck : List String := ["Bool.false_and","FixedLengthPKScheme.indCodec_eq_bitCodec","FixedLengthScheme.decOpen_cpa","FixedLengthScheme.ofFn_splitHalf_fst","FixedLengthScheme.ofFn_splitHalf_snd","List.headD_cons","List.headD_nil","List.length_nil","List.length_ofFn","OracleComp.bind_assoc","OracleComp.pure_bind","PolyExpr.eval_add","PolyExpr.eval_const","S.adaptiveIndGame_eq","S.adaptiveIndImpl_challenge_encrypt","S.adaptiveIndImpl_challenge_full","S.adaptiveIndImpl_challenge_zero","S.adaptiveIndImpl_dec_other","S.inLens_one","S.inLens_zero","S.indImpl_challenge_repeat_onSpec","S.indImpl_dec_onSpec","S.outLens_one","S.outLens_zero","acDin_one","acDin_zero","acDout_one","acDout_zero","acEnc_eq","acHyb_eq","adaptiveIndGame_eq_acHyb","castImpl_adaptiveIndImpl","castImpl_eq","hdec","headD_ofFn_one","hx","hybImpl_congr","hybImpl_fresh","hybImpl_full","hybImpl_zero","if_neg","if_pos","key","msgOf_eq","ofFn_cast","ofFn_padFin_of_length","ofFn_select","padFin_ofFn_zeroBits"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

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

end TCSlib.Cryptography.Composability.AdaptiveCPA
