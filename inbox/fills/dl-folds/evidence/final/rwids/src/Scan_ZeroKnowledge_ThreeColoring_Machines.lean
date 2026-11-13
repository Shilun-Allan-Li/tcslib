import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
open Lean Elab Command

namespace TCSlib.Cryptography.ColMachines
open Complexity Turing Complexity.StateLoop TCSlib.Cryptography.EncodingMachines

def idsToCheck : List String := ["Bool.and_eq_true","CountLoop.acc_def","CountLoop.orbit_eq","CountLoop.out_def","Equiv.apply_symm_apply","Fin.cast_mk","Fin.coe_castSucc","Function.comp_apply","Function.iterate_succ_apply","Function.iterate_succ_apply'","List.append_nil","List.drop_eq_getElem_cons","List.drop_length","List.drop_nil","List.drop_succ_cons","List.filter_append","List.filter_cons","List.filter_map","List.filter_nil","List.findSome?_eq_none_iff","List.findSome?_eq_some_iff","List.flatMap_append","List.flatMap_cons","List.flatMap_map","List.flatMap_singleton","List.foldl_append","List.foldl_cons","List.foldl_nil","List.getD_eq_getElem?_getD","List.getElem?_append","List.getElem?_append_left","List.getElem?_append_right","List.getElem?_drop","List.getElem?_eq_getElem","List.getElem?_map","List.getElem?_replicate","List.getElem?_take_of_lt","List.getElem_finRange","List.getElem_ofFn","List.getElem_take","List.getLast?_eq_getElem?","List.getLastD_eq_getLast?","List.get_eq_getElem","List.head?_drop","List.headD_eq_head?_getD","List.length_append","List.length_cons","List.length_drop","List.length_eq_zero_iff","List.length_map","List.length_replicate","List.length_take","List.map_coe_finRange","List.map_findSome?","List.map_flatMap","List.map_map","List.ofFn_succ_last","List.range_add","List.range_succ","List.replicate_succ","List.take_append_drop","NUPPT.advInput_eq","NUPPT.layout_eq","NUPPT.runAtL_ofPolyTimeUniform","Nat.add_mul_div_left","Nat.add_mul_mod_self_left","Nat.div_eq_of_lt","Nat.le_zero.1","Nat.mod_eq_of_lt","Nat.sub_self","Nat.succ_mul","Option.getD_some","Option.map_some","Option.some.injEq","PolyExpr.eval_add","PolyExpr.eval_const","PolyExpr.eval_mul","PolyExpr.eval_normal","Strategy.encodeMsgs_cons","Strategy.encodeMsgs_nil","Strategy.ofNUPPT_next","Strategy.pairFstD_encodeMsgs","argM","argX","argZ","bitsToNat_def","bitsToNat_eq_natOfBits","colorFromTable","countTrue_succ","cstep_iterate","decColor_def","decColoring_val","decColoring_val_eq","decGraph_apply","decGraph_fst","decide_eq_false_iff_not","decide_eq_true_eq","divNum_eq","edgeAt_def","edgeCount_eq","edgeList_def","edgeOf_eq","encColorOfVal","encColor_def","encColor_eq","encColoring_eq","encGraph_def","encodeMsgs_eq_flatMap","encodeMsgs_eq_nil_iff","filter_range_succ","finProdFinEquiv_apply_val","flatMap_range_ite","flatMap_range_mul","getD_padTo","getElem?_filter_range_nthTrue","h","h0","h1","hb","hbit","hc","hclosed","hcnt","hf","hi","histLen","horb","hw","hx","if_neg","if_pos","ih","ilayout","ilayout_def","iterate_pairSndD_encodeMsgs","length_encGraph","length_filter_range","length_padTo","length_pairEncode","loopState_succ","loopState_zero","map_edgeList","map_product_finRange","map_val_sampleIdx","map_val_sampleIdx_getD","min_eq_left","min_eq_right","modNum_eq","natOfBits_succ","ofFn_eq_map_range","ofFn_padFin","padFin_apply","padFin_def","padTo","pairEncode_eq","pairEncode_eq_append_nil","pairFstD_pairEncode","pairSndD_of_pairDecode_eq_none","pairSndD_pairEncode","permTable","pow_succ","rejectionSample_def","sampleIdx_def","samplePerm3_def","sampleVal","show","tableOfIdx","uniformFromBits_def","upd","zero_add"]
def scannedModule : Name := `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines

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

end TCSlib.Cryptography.ColMachines
