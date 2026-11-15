import lean_proof.scot.base.ObliviousTransferBase
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["Bool.false_eq_true","Equiv.symm_apply_apply","Function.comp_apply","List.getElem_ofFn","List.getElem_take","List.length_ofFn","List.length_take","List.ofFn_const","NUPPT.advInput_eq","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","Protocol.outP_eq","Protocol.outV_eq","Protocol.transcriptWith_eq","T.f_perm","T.inv.coinLen_eq","T.sample.coinLen_eq","coinSeg","exec_succ","exec_zero","hAr","hBr","hHinv","hHw","heval","hg","hknown","hs1","hyb","if_false","if_true","otKnown","otMask","otProtocol","otReceiver","otSender","otSimA","otSimAFun","otSimB","otSimBFun","otSimZ","otSimZb","pairFstD_pairEncode","pairSndD_pairEncode","simIdx","simSample"]
def scannedModule : Name := `lean_proof.scot.base.ObliviousTransferBase

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

end TCSlib.Cryptography.SecureComputation
