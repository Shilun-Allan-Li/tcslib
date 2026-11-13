import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability.FixedLengthPKScheme

def idsToCheck : List String := ["BinArith.hasFalse_eq","Bool.and_eq_true","Bool.not_eq_true'","FixedLengthScheme.decOpen_cca2","FixedLengthScheme.decOpen_cpa","Function.comp_apply","List.any_eq_false","List.length_ofFn","List.length_replicate","List.length_singleton","List.mem_map","NUPPT.advInput_eq","NUPPT.coinsCongr_ofFn","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","PublicKeyScheme.padded_enc","S.correct","S.inLens_one","S.inLens_zero","S.indImpl_challenge_none_onSpec","S.indImpl_challenge_repeat_onSpec","S.indImpl_dec_onSpec","S.indSpec_dom","S.indSpec_rng","S.outLens_one","S.outLens_zero","and_imp","cast_eq","decide_eq_true_eq","decodeFin_ofFn","forall_exists_index","h","h0","hall","henc.runAt_eq","hlen","hm","hnil","hw","h₁","id_eq","indImpl","isPadded","isPadded_padCt","length_pairEncode","padCt","padDecFun","padDecFun_padCt","padEncFun","padEncFun_eq","padEnc_coins","pairFstD_pairEncode","pairSndD_pairEncode","runAt_padEnc","show"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (c : Name) : Name :=
    ((env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!).getD scannedModule
  for s in idsToCheck do
    let n := s.toName
    let cands ← liftCoreM <| (realizeGlobalConstWithInfos (mkIdent n)) <|> (Pure.pure [] : CoreM (List Name))
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

end TCSlib.Cryptography.Composability
