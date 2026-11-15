import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines
open ComposeMachines
open TCSlib.Cryptography.SecureComputation.ComposeMachines
open TCSlib.Cryptography.SecureComputation.HybridProtocol

def idsToCheck : List String := ["Bool.and_eq_true","Compose.runTape_eq","GI.argM_ilayout","GI.argX_ilayout","GI.argZ_ilayout","GI.ilayout_def","GI.inCoins_ilayout","GI.iterate_pairSndD_encodeMsgs","GI.msgCount_encodeMsgs","H.runInputA_of_lt","H.runInputB_of_lt","List.flatMap_def","List.flatMap_map","List.length_replicate","List.map_coe_finRange","List.ofFn_eq_map","Nat.mul_zero","PolyExpr.eval_var","ansW_eq","ansW_ilayout","answersFromA_eq","answersFromB_eq","beq_false","beq_true","composePW_eq","composeP_next","composeVW_eq","composeV_next","decide_eq_true_eq","divNum_eq","encodeMsgs_slotMsgs","flatten_ofFn_eq_flatMap_range","h","hFm","hFρ","hcall","hp","hrun","if_neg","if_pos","mainW_eq","mainW_ilayout","modNum_eq","moverIsV_def","moverW_eq","ofFn_padFin","pairFstD_pairEncode","pairSndD_pairEncode","runNextA_eq","runNextB_eq","runW_eq","runW_ilayout"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency

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
