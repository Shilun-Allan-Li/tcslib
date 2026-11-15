import TCSlib.Cryptography.Authentication.MAC.FromPRF
open Lean Elab Command

namespace TCSlib.Cryptography.Authentication
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

def idsToCheck : List String := ["Function.comp_apply","List.length_ofFn","List.singleton_inj","MAC.accepts_iff","MAC.secure_iff","NUPPT.advInput_eq","NUPPT.coinsEquivPoly_ofFn","NUPPT.coins_ofPolyTimeUniform","NUPPT.inArg_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","PolyExpr.eval_var","atParam_eq","decide_eq_true_iff","decide_true","eq_self_iff_true","hEF","hFE","hgen","hk","hkey","hmsg","htagE","ofFn_padFin_of_length","padFin_ofFn","pairFstD_pairEncode","pairSndD_pairEncode","prfMAC_gen","prfMAC_msgLen","prfMAC_tagLen","prfMAC_ver","prfTagFun_eq","prfVerFun","prfVerFun_eq","runAt_coinKey"]
def scannedModule : Name := `TCSlib.Cryptography.Authentication.MAC.FromPRF

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

end TCSlib.Cryptography.Authentication
