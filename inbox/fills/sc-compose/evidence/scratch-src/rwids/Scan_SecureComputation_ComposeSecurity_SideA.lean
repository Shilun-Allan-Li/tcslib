import TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideA
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Finset Complexity Turing TCSlib.Cryptography ComposeMachines ComposeSim ComposeProb
open TCSlib.Cryptography.SecureComputation.HybridProtocol

def idsToCheck : List String := ["Functionality.idealA_eq","Functionality.realA_eq","H.acceptProb_realA_dPhi","H.realA_compose_eq","Hd","List.getElem_ofFn","List.length_map","List.length_ofFn","List.length_range","List.length_replicate","List.map_map","NUPPT.coinLen_eq","NUPPT.runAtL_eq_output_layout","NUPPT.runAt_eq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_var","Protocol.transcript_eq_transcriptWith","Protocol.viewP_eq","Strategy.coinLen_eq","View.encode_mk","acceptProb_comp_equiv","acceptProb_pre","answersA_eq","asmW_pairEncode","coinBlock_blocksCoins","coinBlock_flatten","dif_pos","distAdv_def","e3","getD_plug","hV","hc","hcall","hfill","hid","hreal","hsim","hybV_eq","inA_val","inB_val","le_refl","length_pairEncode","msgAt_encodeMsgs","pairFstD_pairEncode","phiD_pairEncode","phiV_view","plugV_eq","privA_eq","realA_eq","realViewA_eq","sampleA_eq","simRunA_eq","tmplW_eq","viewRunA_eq"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.SideA

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

end TCSlib.Cryptography.SecureComputation
