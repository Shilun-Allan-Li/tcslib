import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeProb
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["ComposeSim.ofFn_blocks_symm","Equiv.trans_apply","List.drop_left'","List.getElem_ofFn","List.length_ofFn","List.take_left'","NUPPT.advInput_eq","NUPPT.coinLen_eq","NUPPT.distinguisherL_eq","NUPPT.inAdvice_layout","NUPPT.inArg_layout","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTime","NUPPT.runAt_eq","PolyExpr.eval_add","acceptProb_def","acceptProb_pre","appendCoins_eq","blocksCoins_eq","coinBlock_flatten","drop_ofFn_appendCoins","h","hB","hS","hSc","hc","hΨ","ofFn_appendCoins","ofFn_arrowCongr_finCongr","ofFn_blocksCoins","take_ofFn_appendCoins"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept

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

end TCSlib.Cryptography.SecureComputation.ComposeProb
