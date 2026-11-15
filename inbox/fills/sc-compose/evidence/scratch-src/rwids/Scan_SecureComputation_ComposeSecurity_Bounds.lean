import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeBound
open Complexity Turing

def idsToCheck : List String := ["BinArith.encWords_def","Compose.exec_eq_map","ComposeMachines.encodeMsgs_eq_flatMap","GI.ilayout_def","List.length_map","List.length_nil","List.length_ofFn","List.length_replicate","NUPPT.layout_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","NUPPT.timeBound_def","Nat.add_zero","Protocol.transcriptWith_eq","hnext","length_layout","length_pairEncode"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds

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

end TCSlib.Cryptography.SecureComputation.ComposeBound
