import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeSim
open Finset Complexity Turing TCSlib.Cryptography ComposeProb ComposeMachines

def idsToCheck : List String := ["List.length_nil","Strategy.encodeMsgs_cons","acceptProb_pre","dif_neg","dif_pos","distAdv_def","encodeMsgs_append","hybW_eq","hybW_tmplW","key","pairFstD_pairEncode","pairSndD_pairEncode","tmplW_eq","β"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Template

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
