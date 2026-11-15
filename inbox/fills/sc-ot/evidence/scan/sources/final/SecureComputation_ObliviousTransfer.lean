import TCSlib.Cryptography.SecureComputation.ObliviousTransfer
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing TCSlib.Cryptography

def idsToCheck : List String := ["Bool.false_eq_true","Equiv.symm_apply_apply","Function.comp_apply","List.getElem_ofFn","List.getElem_take","List.length_ofFn","List.length_take","List.ofFn_const","NUPPT.advInput_eq","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTimeUniform","NUPPT.runAt_eq","OT.mask_eq","OT.receiverNext_eq","OT.senderNext_eq","OT.simAView_eq","OT.simBView_eq","OT.simIndex_eq","OT.simSampled_eq","OT.simSeg_eq","OT.simZbit_eq","OT.simZpair_eq","Protocol.outP_eq","Protocol.outV_eq","Protocol.transcriptWith_eq","T.f_perm","T.inv.coinLen_eq","T.sample.coinLen_eq","coinSeg","coinSeg_eq","exec_succ","exec_zero","hAr","hBr","hHinv","hHw","heval","hg","hknown","hs1","hyb","if_false","if_true","otKnown","otKnown_eq","otMask","otMask_eq","otProtocol","otProtocol_P","otProtocol_V","otRaw_eq","otReceiver","otReceiver_coins","otReceiver_next","otSender","otSender_coins","otSender_next","otSimA","otSimAFun","otSimAFun_eq","otSimB","otSimBFun","otSimBFun_eq","otSimZ","otSimZ_eq","otSimZb","otSimZb_eq","pairFstD_pairEncode","pairSndD_pairEncode","runAt_otSimA","runAt_otSimB","simIdx","simIdx_eq","simSample","simSample_eq"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ObliviousTransfer

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
