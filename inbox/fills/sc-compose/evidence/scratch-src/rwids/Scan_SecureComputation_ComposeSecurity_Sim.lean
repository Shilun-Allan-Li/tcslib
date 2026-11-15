import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeSim
open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines ComposeMachines

def idsToCheck : List String := ["Compose.getD_map_range","List.flatMap_map","List.length_replicate","asmW_pairEncode","encodeMsgs_eq_flatMap","msgAt_encodeMsgs","pairFstD_pairEncode","pairSndD_pairEncode","phiD","phiV_eq","simV","simV_pairEncode","vlW_eq"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim

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
