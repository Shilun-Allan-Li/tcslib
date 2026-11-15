import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.OT
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["List.headD_cons","PolyExpr.eval_const","Protocol.transcriptWith_eq","exec_succ","exec_zero","hP","hV","hf","hr","h₁","h₂","h₃","h₄","h₅","if_neg","if_pos","moverIsV_false","receiverNext_eq","receiverNext_pair","senderNext_eq","senderNext_nil","senderNext_pair"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape

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
