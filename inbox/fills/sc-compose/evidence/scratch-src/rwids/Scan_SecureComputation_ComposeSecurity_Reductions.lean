import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeSim
open Complexity Turing Complexity.NUPPT

def idsToCheck : List String := ["List.length_replicate","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","advInput_eq","coinLen_eq","inAdvice_layout","inArg_layout","inCoins_layout","inParam_layout","layout_eq","length_pairEncode","pairFstD_pairEncode","pairSndD_pairEncode","runAtL_eq_output_layout","runAtL_ofPolyTime"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions

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

end TCSlib.Cryptography.SecureComputation.ComposeSim
