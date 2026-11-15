import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
open Lean Elab Command

namespace TCSlib.Cryptography.SecureComputation.ComposeMachines
open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

def idsToCheck : List String := ["BinArith.pairEncode_nil_append","Compose.slotMsgs_eq","Fin.val_mk","Function.comp_apply","GI.ilayout_def","GI.iterate_pairSndD_encodeMsgs","List.append_assoc","List.append_nil","List.cons_append","List.filter_append","List.filter_nil","List.filter_singleton","List.flatMap_append","List.flatMap_cons","List.flatMap_map","List.flatMap_nil","List.flatMap_singleton","List.getD_eq_getElem?_getD","List.getElem?_append","List.getElem?_eq_getElem","List.getElem?_eq_none_iff.2","List.getElem?_ofFn","List.getElem?_replicate","List.getElem?_take","List.head?_drop","List.headD_eq_head?_getD","List.length_append","List.length_replicate","List.length_take","List.nil_append","List.range_succ","List.range_zero","NUPPT.Uniform.advice_eq","NUPPT.runAtL_eq_output_layout","Option.getD_none","Option.getD_some","PolyExpr.eval_normal","PolyExpr.eval_var","Strategy.encodeMsgs_cons","Strategy.encodeMsgs_nil","Strategy.ofNUPPT_next","Strategy.pairFstD_encodeMsgs","cond_false","cond_true","cstep_iterate","decide_eq_true_eq","dif_neg","dif_pos","encodeMsgs_eq_flatMap","flatMap_range_ite","h","hclosed","hnext","horb","if_neg","if_pos","ih","length_pairEncode","min_eq_right","msgAt_encodeMsgs","padFin_apply","padTo_eq","pairFstD_pairEncode","pairSndD_pairEncode","show"]
def scannedModule : Name := `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

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

end TCSlib.Cryptography.SecureComputation.ComposeMachines
