import lean_proof.ett.base.EncryptThenTagBase
open Lean Elab Command

namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Function.comp_apply","List.append_nil","List.cons.injEq","List.length_append","List.length_ofFn","List.replicate_zero","List.zipWith_cons_cons","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.coins_ofPolyTimeUniform","NUPPT.inArg_eq","NUPPT.inCoins_eq","NUPPT.inParam_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Nat.sub_self","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","ccaDecFun","ccaDecOK","ccaEncFun","ccaGenFun","ccaMaskFun","decodeFin_ofFn","hA","hB","hFE","ha","hb","hc₁","hp","hr","ht","htag","hρ","length_pairEncode","runAt_ccaDec","runAt_ccaEnc","runAt_ccaGen","zipWith_xor_xor_self'"]
def scannedModule : Name := `lean_proof.ett.base.EncryptThenTagBase

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

end TCSlib.Cryptography.Composability
