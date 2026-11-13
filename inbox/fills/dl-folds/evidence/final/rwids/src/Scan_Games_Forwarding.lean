import TCSlib.Cryptography.Games.Forwarding
open Lean Elab Command

namespace TCSlib.Cryptography.Games
open Complexity Turing
open InteractiveHandler
open InteractiveHandler
open TCSlib.Cryptography.Games.InteractiveHandler

def idsToCheck : List String := ["InteractiveHandler.rAns_input","InteractiveHandler.rI_input","InteractiveHandler.rL_input","InteractiveHandler.rS_input","InteractiveHandler.rX_input","NUPPT.runAt_coinsCongr","NUPPT.runAt_eq","NUPPT.toCompOn_eq","PolyExpr.eval_const","fwdHandler_perCall","fwdRun","hB'","hB₁","hrun","hrun₁","id_eq","if_neg","if_pos","ofFn_padFin_of_length","pairFstD_pairEncode","pairSndD_pairEncode"]
def scannedModule : Name := `TCSlib.Cryptography.Games.Forwarding

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

end TCSlib.Cryptography.Games
