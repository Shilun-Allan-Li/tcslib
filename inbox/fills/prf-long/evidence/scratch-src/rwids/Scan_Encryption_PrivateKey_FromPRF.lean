import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
open Lean Elab Command

namespace TCSlib.Cryptography
open Complexity Turing Finset

def idsToCheck : List String := ["Bool.and_eq_false_iff","Function.comp_apply","List.cons.injEq","List.flatMap_cons","List.flatMap_nil","List.length_ofFn","List.length_replicate","List.zipWith_cons_cons","NUPPT.advInput_eq","NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","PolyExpr.eval_var","PrivateKeyScheme.encodeList_cons","PrivateKeyScheme.encodeList_nil","PrivateKeyScheme.multiEncDist_apply","acceptProb_comp_equiv","decide_eq_false_iff_not","decodeFin_eq","decodeFin_ofFn","distAdv_def","encodeList_eq_flatMap","encodeTuple","encodeTupleOut_eq","encodeTuple_eq_encodeTupleOut","h","h1","h2","hFE","hc","hf","hr","key","pairEncode_eq","pairFstD_pairEncode","pairSndD_pairEncode","prfDecFun","prfDecWF","prfEncFun","prfEncReal_apply","prfEncReal_eq_prfEncRealOut","prfScheme_multiEncDist","runAt_coinKey","runAt_prfDec","runAt_prfEnc","zipWith_xor_ofFn_add","zipWith_xor_xor_self"]
def scannedModule : Name := `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF

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

end TCSlib.Cryptography
