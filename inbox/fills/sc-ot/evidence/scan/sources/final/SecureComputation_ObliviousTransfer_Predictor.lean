import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.OT
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["List.drop_left'","List.headD_cons","List.length_replicate","List.take_left'","NUPPT.Uniform.advice_eq","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.distinguisherL_eq","NUPPT.inAdvice_layout","NUPPT.inArg_layout","NUPPT.inCoins_layout","NUPPT.inParam_layout","NUPPT.layout_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_eq","PolyExpr.eval_add","length_ofFn_coins","pairFstD_pairEncode","pairSndD_pairEncode","runAtL_viewDist","viewDist","viewDistCoins_symm_ofFn","viewDistRaw_eq","viewDist_coins","viewRaw_eq"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor

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

end TCSlib.Cryptography.SecureComputation.OT
